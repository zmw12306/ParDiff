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


#include "Core/LoopSummaryStateMachine.h"
#include "Support/Debug.h"

raw_ostream &operator<<(raw_ostream &O, const LoopSummaryStateMachine &FSM) {
    unsigned K = 0;
    for (auto *S: FSM) {
        O << "<state " << K << ">\n";
        O << *S << "\n";
        O << "</state " << K << ">\n";
        O << "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^";
        K++;
    }
    return O;
}

LoopSummaryState *LoopSummaryStateMachine::rootState() const {
    if (RootStates.size() != 1) return nullptr;
    return *RootStates.begin();
}

LoopSummaryState *LoopSummaryStateMachine::newState(unsigned ID) {
    auto *Ret = new LoopSummaryState(CurrLoop, ID);
    AllStates.push_back(Ret);
    if (RootStates.empty()) {
        RootStates.insert(Ret);
    }
    for (auto *CS: CurrStates) {
        CS->NextStates.insert(Ret);
        Ret->PrevStates.insert(CS);
    }
    CurrStates.clear();
    CurrStates.insert(Ret);
    return Ret;
}

LoopSummaryState *LoopSummaryStateMachine::recentNewState() const {
    return AllStates.back();
}

void LoopSummaryStateMachine::summarizeRecentNewState() {
    unsigned SummarizationResult = 0;
    auto *NewState = recentNewState();
    assert(NewState && NewState == AllStates.back());
    assert(NewState->NextStates.empty());
    if (NewState->PrevStates.empty()) {
        assert(AllStates.size() == 1);
        // this is the first state, we do not need to do anything
    } else if (NewState->PrevStates.size() == 1) {
        auto *PrevState = *NewState->PrevStates.begin();
        if (*NewState == *PrevState) {
            SummarizationResult = PrevState->summarize(NewState);
            AllStates.pop_back();
            PrevState->NextStates.erase(NewState);
            CurrStates.erase(NewState);
            assert(CurrStates.empty());
            assert(PrevState->NextStates.empty());
            CurrStates.insert(PrevState);
            delete NewState;
        } else {
            pardiff_WARN("[Loop] A different state is discovered, not supported yet!");
            SummarizationResult = 3;
        }
    } else {
        pardiff_WARN("[Loop] Multi-state FSM discovered, not supported yet!");
        SummarizationResult = 3;
    }

    // we have summarized a new state, test if we finish summarizing or fail to summarize
    switch (SummarizationResult) {
        case 0:
        case 1:
            assert(FSMStatus == LSSM_Summarizing);
            break;
        case 2:
            FSMStatus = LSSM_Summarized;
            break;
        case 3:
            FSMStatus = LSSM_Fail2Summarize;
            break;
        default:
            llvm_unreachable("Error: unknown summarizing status!");
    }
}
