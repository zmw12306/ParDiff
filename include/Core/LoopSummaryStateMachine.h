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


#ifndef CORE_LOOPSUMMARYSTATEMACHINE_H
#define CORE_LOOPSUMMARYSTATEMACHINE_H

#include "Core/ExecutionState.h"
#include "Core/LoopSummaryState.h"

class LoopSummaryStateMachine {
private:
    /// current loop
    SingleLoop *CurrLoop;

    /// collect all states
    std::vector<LoopSummaryState *> AllStates;

    /// the current states, which will transit to new states
    std::set<LoopSummaryState *> RootStates;
    std::set<LoopSummaryState *> CurrStates;

    /// running status of the loop summary state machine
    /// @{
    enum LSSMStatus {
        LSSM_Summarizing,
        LSSM_Fail2Summarize,
        LSSM_Summarized
    };

    LSSMStatus FSMStatus;
    /// @}

public:
    LoopSummaryStateMachine(SingleLoop *L) : CurrLoop(L), FSMStatus(LSSM_Summarizing) {}

    LoopSummaryState *rootState() const;

    LoopSummaryState *newState(unsigned LID);

    LoopSummaryState *recentNewState() const;

    void summarizeRecentNewState();

    LSSMStatus status() const { return FSMStatus; }

    bool empty() const { return AllStates.empty(); }

    unsigned size() const { return AllStates.size(); }

    std::vector<LoopSummaryState *>::const_iterator begin() const {
        return AllStates.begin();
    }

    std::vector<LoopSummaryState *>::const_iterator end() const {
        return AllStates.end();
    }

    std::set<LoopSummaryState *>::const_iterator root_state_begin() const {
        return RootStates.begin();
    }

    std::set<LoopSummaryState *>::const_iterator root_state_end() const {
        return RootStates.end();
    }

    std::set<LoopSummaryState *>::const_iterator curr_state_begin() const {
        return CurrStates.begin();
    }

    std::set<LoopSummaryState *>::const_iterator curr_state_end() const {
        return CurrStates.end();
    }

public:
    friend class LoopSummaryAnalysis;

    friend raw_ostream &operator<<(llvm::raw_ostream &, const LoopSummaryStateMachine &);
};

raw_ostream &operator<<(llvm::raw_ostream &, const LoopSummaryStateMachine &);

#endif //CORE_LOOPSUMMARYSTATEMACHINE_H
