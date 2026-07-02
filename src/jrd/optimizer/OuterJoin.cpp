/*
 *  The contents of this file are subject to the Initial
 *  Developer's Public License Version 1.0 (the "License");
 *  you may not use this file except in compliance with the
 *  License. You may obtain a copy of the License at
 *  http://www.ibphoenix.com/main.nfs?a=ibphoenix&page=ibp_idpl.
 *
 *  Software distributed under the License is distributed AS IS,
 *  WITHOUT WARRANTY OF ANY KIND, either express or implied.
 *  See the License for the specific language governing rights
 *  and limitations under the License.
 *
 *  The Original Code was created by Dmitry Yemanov
 *  for the Firebird Open Source RDBMS project.
 *
 *  Copyright (c) 2023 Dmitry Yemanov <dimitr@firebirdsql.org>
 *  and all contributors signed below.
 *
 *  All Rights Reserved.
 *  Contributor(s): ______________________________________.
 *
 */

#include "firebird.h"

#include "../jrd/jrd.h"
#include "../jrd/cmp_proto.h"
#include "../jrd/RecordSourceNodes.h"
#include "../jrd/recsrc/RecordSource.h"

#include "../jrd/optimizer/Optimizer.h"

using namespace Firebird;
using namespace Jrd;


//
// Constructor
//

OuterJoin::OuterJoin(thread_db* aTdbb, Optimizer* opt,
					 const RseNode* rse, RiverList& rivers,
					 SortNode** sortClause)
	: PermanentStorage(*aTdbb->getDefaultPool()),
	  tdbb(aTdbb),
	  optimizer(opt),
	  csb(opt->getCompilerScratch()),
	  sortPtr(sortClause)
{
	// Loop through the join sub-streams. Do it backwards, as rivers are passed as a stack.

	fb_assert(rse->rse_relations.getCount() == 2);
	fb_assert(rivers.getCount() <= 2);

	for (int pos = 1; pos >= 0; pos--)
	{
		auto node = rse->rse_relations[pos];
		auto& joinStream = joinStreams[pos];
		joinStream.node = node;

		if (nodeIs<RelationSourceNode>(node) || nodeIs<LocalTableSourceNode>(node))
		{
			const auto stream = node->getStream();
			fb_assert(!(csb->csb_rpt[stream].csb_flags & csb_active));
			joinStream.number = stream;
		}
		else
		{
			joinStream.river = rivers.pop();
		}
	};

	fb_assert(rivers.isEmpty());

	// Determine which stream should be outer and which is inner.
	// In the case of a left join, the syntactically left stream is the outer,
	// and the right stream is the inner. For a right join, just swap the sides.
	// For a full join, the order does not matter, but given the first outer join
	// is already compiled, let's better preserve the original order.

	if (rse->rse_jointype == blr_right)
	{
		// RIGHT JOIN is converted into LEFT JOIN by the BLR parser,
		// so it should never appear here
		fb_assert(false);
		std::swap(joinStreams[0], joinStreams[1]);
	}
}


// Generate a top level outer join. The "outer" and "inner" sub-streams must be
// handled differently from each other. The inner is like other streams.
// The outer one isn't because conjuncts may not eliminate records from the stream.
// They only determine if a join with an inner stream record is to be attempted.

RecordSource* OuterJoin::generate()
{
	const auto outerJoinRsb = process();

	if (!optimizer->isFullJoin())
		return outerJoinRsb;

	auto& outer = joinStreams[0];
	auto& inner = joinStreams[1];

	StreamList outerStreams, innerStreams;
	outer.getStreams(outerStreams);
	inner.getStreams(innerStreams);

	// A FULL JOIN B is currently implemented similar to:
	//
	// (A LEFT JOIN B)
	// UNION ALL
	// (B LEFT JOIN A WHERE A.* IS NULL)
	//
	// See also FullOuterJoin class implementation.
	//
	// At this point we already have the first part -- (A LEFT JOIN B) -- ready,
	// so just swap the sides and make the second (reversed) join.

	std::swap(outer, inner);

	// Reset both streams to their original states

	for (const auto stream : outerStreams)
		csb->csb_rpt[stream].deactivate();

	outer.river = nullptr;

	for (const auto stream : innerStreams)
		csb->csb_rpt[stream].deactivate();

	inner.river = nullptr;

	// Clone the booleans to make them re-usable for a reversed join

	for (auto iter = optimizer->getConjuncts(); iter.hasData(); ++iter)
	{
		if (iter & Optimizer::CONJUNCT_USED)
			iter.reset(CMP_clone_node_opt(tdbb, csb, iter));
	}

	const auto reversedJoinRsb = process();

	// Allocate and return the final join record source

	return FB_NEW_POOL(getPool()) FullOuterJoin(csb, outerJoinRsb, reversedJoinRsb, outerStreams);
}


RecordSource* OuterJoin::process()
{
	BoolExprNode* boolean = nullptr;

	auto& outer = joinStreams[0];
	auto& inner = joinStreams[1];

	// Generate record sources for the sub-streams.
	// For the outer sub-stream we also will get a boolean back.

	RecordSource* outerRsb = nullptr;
	RecordSource* innerRsb = nullptr;

	if (outer.number != INVALID_STREAM)
	{
		outerRsb = optimizer->generateRetrieval(outer.number,
			optimizer->isFullJoin() ? nullptr : sortPtr, true, false, &boolean);
	}
	else
	{
		if (outer.river)
			outerRsb = outer.river->getRecordSource();
		else
		{
			fb_assert(optimizer->isFullJoin());

			outerRsb = outer.node->compile(tdbb, optimizer, false);
		}

		// Collect booleans computable for the outer sub-stream, it must be active now
		boolean = optimizer->composeBoolean();
	}

	fb_assert(outerRsb);

	// Check whether the inner sub-stream is better joined using the hash join
	// algorithm rather than per-record retrievals inside a nested loop join

	if (!optimizer->isFullJoin())
	{
		if (const auto hashJoinRsb = generateHashJoin(outerRsb, boolean))
			return hashJoinRsb;
	}

	if (inner.number != INVALID_STREAM)
	{
		// AB: the sort clause for the inner stream of an OUTER JOIN
		//	   should never be used for the index retrieval
		innerRsb = optimizer->generateRetrieval(inner.number, nullptr, false, true);
	}
	else
	{
		if (inner.river)
			innerRsb = inner.river->getRecordSource();
		else
		{
			fb_assert(optimizer->isFullJoin());

			StreamList outerStreams;
			outerRsb->findUsedStreams(outerStreams);
			optimizer->setOuterStreams(outerStreams);

			innerRsb = inner.node->compile(tdbb, optimizer, true);
		}
	}

	fb_assert(innerRsb);

	// Generate a parent filter record source for any remaining booleans that
	// were not satisfied via an index lookup

	innerRsb = optimizer->applyResidualBoolean(innerRsb);

	// Allocate and return the join record source

	return FB_NEW_POOL(getPool()) NestedLoopJoin(csb, outerRsb, innerRsb, boolean);
};


//
// Attempt to generate a hash join for the outer join. This pays off when the
// outer sub-stream is expected to produce many records, as it avoids a per-record
// index retrieval of the inner sub-stream (or, worse, a per-record full scan of it,
// if the join condition cannot be mapped to any index). The decision is cost-based.
// Returns nullptr if hash joining is either impossible (no suitable equi-join
// condition exists) or estimated to be more expensive than the nested loop join.
//

RecordSource* OuterJoin::generateHashJoin(RecordSource* outerRsb, BoolExprNode* boolean)
{
	auto& inner = joinStreams[1];

	// Only a single-table inner sub-stream is currently supported
	if (inner.number == INVALID_STREAM)
		return nullptr;

	// A hash join caches the whole inner stream before returning the first record,
	// so avoid it if the prompt first-record delivery was requested
	if (optimizer->favorFirstRows())
		return nullptr;

	// Allow disabling this optimization via the configuration file
	if (!tdbb->getDatabase()->dbb_config->getOuterHashJoin())
		return nullptr;

	const auto innerStream = inner.number;
	const auto tail = &csb->csb_rpt[innerStream];

	// Respect the user-specified access plan, if any
	if (tail->csb_plan)
		return nullptr;

	StreamList outerStreamList;
	joinStreams[0].getStreams(outerStreamList);

	// Scan the conjuncts applicable to the inner sub-stream, looking for equi-join
	// conditions between the outer and inner sub-streams

	tail->activate();

	const auto outerKeys = FB_NEW_POOL(getPool()) NestValueArray(getPool());
	const auto innerKeys = FB_NEW_POOL(getPool()) NestValueArray(getPool());

	for (auto iter = optimizer->getConjuncts(false, true); iter.hasData(); ++iter)
	{
		if (iter & Optimizer::CONJUNCT_USED)
			continue;

		// Residual conjuncts (e.g. booleans of the unnested subqueries) cannot be
		// composed into the hash join condition, so refuse hash joining. Also refuse
		// it if some conjunct referring the inner stream is not computable using our
		// two sub-streams, whatever unexpected it could be.

		if (!iter->computable(csb, INVALID_STREAM, false))
		{
			if (iter->containsStream(innerStream))
			{
				tail->deactivate();
				return nullptr;
			}

			continue;
		}

		if (iter->nodFlags & ExprNode::FLAG_RESIDUAL)
		{
			tail->deactivate();
			return nullptr;
		}

		NestConst<ValueExprNode> node1;
		NestConst<ValueExprNode> node2;

		if (optimizer->getEquiJoinKeys(*iter, &node1, &node2))
		{
			// The hashed (inner) side of the key must reference only the inner
			// stream, as it's evaluated while caching the inner records, i.e.
			// while the outer streams are not positioned yet

			if (!node2->containsStream(innerStream, true))
			{
				if (!node1->containsStream(innerStream, true))
					continue;

				std::swap(node1, node2);
			}

			if (!node1->containsStream(innerStream) &&
				node1->containsAnyStream(outerStreamList))
			{
				outerKeys->add(node1);
				innerKeys->add(node2);
			}
		}
	}

	if (!outerKeys->hasData())
	{
		tail->deactivate();
		return nullptr;
	}

	// Estimate the cost of the nested loop join, i.e. a per-record dependent
	// retrieval of the inner stream (the outer streams are active at this point)

	const auto streamCardinality = tail->csb_cardinality;
	const double outerCardinality = MAX(outerRsb->getCardinality(), MINIMUM_CARDINALITY);
	double loopCost, matchSelectivity, matchCardinality;
	bool conditional;

	{ // scope
		Retrieval retrieval(tdbb, optimizer, innerStream, false, true, nullptr, true);
		const auto candidate = retrieval.getInversion();

		loopCost = candidate->cost * outerCardinality;
		matchSelectivity = candidate->selectivity;
		matchCardinality = streamCardinality * matchSelectivity;

		if (candidate->unique && matchCardinality > MINIMUM_CARDINALITY)
			matchCardinality = MINIMUM_CARDINALITY;

		conditional = (candidate->condition != nullptr);
	}

	// Estimate the cost of the hash join: an independent retrieval of the inner
	// stream plus hashing it and probing the hash table for every outer record

	double hashCost, hashCardinality;
	bool allowHashJoin;

	{ // scope
		StreamStateHolder stateHolder(csb, outerStreamList);
		stateHolder.deactivate();

		Retrieval retrieval(tdbb, optimizer, innerStream, false, true, nullptr, true);
		const auto candidate = retrieval.getInversion();

		hashCardinality = streamCardinality * candidate->selectivity;

		// If the table looks like empty during preparation time, we cannot be sure
		// about its real cardinality during execution. So, unless we have some
		// index-based filtering applied, let's better be pessimistic and avoid
		// hash joining due to likely cardinality under-estimation.
		// Also, avoid hashing if the stream to be hashed is too large.
		// Beware conditional retrievals, hash joining is impossible for them.

		allowHashJoin =
			(streamCardinality > MINIMUM_CARDINALITY || candidate->indexes) &&
			hashCardinality <= HashJoin::maxCapacity() &&
			!candidate->condition;

		hashCost = candidate->cost +
			// hashing cost
			hashCardinality * (COST_FACTOR_MEMCOPY + COST_FACTOR_HASHING) +
			// probing + copying cost
			outerCardinality * (COST_FACTOR_HASHING + matchCardinality * COST_FACTOR_MEMCOPY);
	}

	// Prefer the hash join if it wins the direct cost comparison. Also prefer it
	// if the inner stream is cheap to cache and hash in absolute terms and the
	// nested loop join does not survive a moderate under-estimation of the outer
	// cardinality (see OUTER_HASH_RISK_MARGIN comments)

	const bool preferHashJoin = (hashCost <= loopCost) ||
		(hashCardinality <= OUTER_HASH_RISK_MAX_CARDINALITY &&
			hashCost <= loopCost * OUTER_HASH_RISK_MARGIN);

	if (conditional || !allowHashJoin || !preferHashJoin)
	{
		tail->deactivate();
		return nullptr;
	}

	// Hash join is preferred. Generate an independent retrieval of the inner stream,
	// it consumes the conjuncts local to the inner stream (they filter the cached
	// records before the null-extension, thus preserving the outer join semantics).

	RecordSource* innerRsb;

	{ // scope
		StreamStateHolder stateHolder(csb, outerStreamList);
		stateHolder.deactivate();

		innerRsb = optimizer->generateRetrieval(innerStream, nullptr, false, true);
	}

	// Compose the remaining conjuncts (the equi-join conditions plus any other join
	// conditions) into the join boolean, to be re-checked by the hash join for every
	// candidate match. It cannot be applied as a filter above the join, as this would
	// break the null-extension semantics.

	BooleanList filters;
	auto iter = optimizer->getConjuncts(false, true);
	const auto joinBoolean = optimizer->composeBoolean(iter, filters);

	// At least the equi-join conditions found above must be present
	fb_assert(joinBoolean);

	// The join boolean filters the joined records, so its filtering effect is
	// already accounted for and its re-applications at the upper RSE levels must
	// not affect the cardinality estimations anymore

	Optimizer::markBooleanCounted(csb, joinBoolean);

	RecordSource* const args[] = {outerRsb, innerRsb};
	NestValueArray* const keys[] = {outerKeys, innerKeys};

	return FB_NEW_POOL(getPool()) HashJoin(tdbb, csb, boolean, joinBoolean,
										   args, keys, matchSelectivity);
}


