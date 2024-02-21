/*
 *  pardiff lifts protocol source code in C to its specification in BNF
 *  Copyright (C) 2022  
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Affero General Public License as published
 *  by the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Affero General Public License for more details.
 *
 *  You should have received a copy of the GNU Affero General Public License
 *  along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */


#ifndef CORE_LOOPSUMMARYANALYSIS_H
#define CORE_LOOPSUMMARYANALYSIS_H

#include "Core/ExecutionState.h"
#include "Core/LoopInformationAnalysis.h"
#include "Core/LoopSummaryState.h"
#include "Core/LoopSummaryStateMachine.h"

typedef std::map<std::pair<BasicBlock *, unsigned>, ExecutionState *> ExitStateMapType;

/// for summarizing a loop to a state machine
class LoopSummaryAnalysis {
private:
    /// the loop for which this analysis is created
    SingleLoop *CurrLoop;

    /// record how many iterations of the loop under analysis
    unsigned TripCount;

    /// an auxiliary variable for recording path conditions
    unsigned PCIndex;

    /// the initial merge id
    unsigned InitialMergeID;

    /// the loop analysis id
    unsigned LoopAnalysisID;

    /// the initial execution state, which will be used to recover the state after loop summarization
    ExecutionState *InitialState;

    /// memory revised at the end of an exiting/latch block
    std::set<AbstractValue *> RevisedMemoryValues;

    /// the state machine
    LoopSummaryStateMachine *FSM;

    /// exiting state [exiting -> exit] -> exiting state
    ExitStateMapType ExitStateMap;

    /// virtual registers that may be used out of a loop iteration
    std::set<Instruction *> EscapedRegisters;

public:
    LoopSummaryAnalysis(SingleLoop *, ExecutionState *, unsigned, unsigned);

    ~LoopSummaryAnalysis();

    void incTripCount();

    unsigned getTripCount() const;

    SingleLoop *getLoop() const { return CurrLoop; }

    /// instrument the static analysis to record information of each loop iteration
    /// @{
    void recordMemoryRevised(AbstractValue *V);

    void recordBytesLoaded(const z3::expr &);
    /// @}

    /// @{
    /// collect result for summarization
    void collect(BasicBlock *B, ExecutionState *ES, unsigned MergID);

    /// collect result from a nested loop, when the nested loop ends
    void collect(LoopSummaryAnalysis *, ExecutionState *ES);
    /// @}

    /// if the loop summary analysis does not finish, we should be able to return
    /// the initial state of the next iteration, given the current state at the loop latch.
    ///
    /// in most cases, it should return the given state directly
    /// if we fall back to unrolling mode from a summarizing mode, we need use the original initial state
    /// so that we can restart the analysis of the loop
    ExecutionState *getNextInitialState(ExecutionState *);

    /// return true if we are in the unrolling mode
    bool inUnrollingMode() const { return !FSM; }

    /// return true if we can finish analyzing a loop and can exit
    bool finish() const;

    /// get the initial merge id
    unsigned getMergeID() const { return InitialMergeID; }

    /// get the analysis id
    unsigned getLoopAnalysisID() const { return LoopAnalysisID; }

public:
    ExitStateMapType::const_iterator exiting_state_begin() const { return ExitStateMap.begin(); }

    ExitStateMapType::const_iterator exiting_state_end() const { return ExitStateMap.end(); }

    std::set<AbstractValue *>::const_iterator revised_mem_begin() const { return RevisedMemoryValues.begin(); }

    std::set<AbstractValue *>::const_iterator revised_mem_end() const { return RevisedMemoryValues.end(); }

private:
    /// after loop summarization, we recompute the exiting loop states
    void recoverExitingStates();
};

#endif //CORE_LOOPSUMMARYANALYSIS_H
