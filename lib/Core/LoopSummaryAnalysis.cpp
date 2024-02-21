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

#include <llvm/Support/CommandLine.h>
#include <llvm/Support/Debug.h>

#include "Core/LoopSummaryAnalysis.h"

#define DEBUG_TYPE "LoopSummaryAnalysis"

using namespace llvm;

static cl::opt<bool> EnableLoopSummary(
        "pardiff-enable-loop-summary",
        cl::desc("use loop summarization technique"),
        cl::init(false));

static cl::opt<unsigned> LoopUnrollCount(
        "pardiff-loop-unroll-count",
        cl::desc("set the unroll count"),
        cl::init(1));

LoopSummaryAnalysis::LoopSummaryAnalysis(SingleLoop *SL, ExecutionState *S, unsigned MID, unsigned LID) :
        CurrLoop(SL), TripCount(0), PCIndex(0), InitialMergeID(MID), LoopAnalysisID(LID) {
    assert(LoopUnrollCount > 0);
    InitialState = nullptr;
    FSM = nullptr;

    if (!EnableLoopSummary.getValue() || !S) return;

    InitialState = S->fork();
    FSM = new LoopSummaryStateMachine(SL);
    for (auto *B: *SL) {
        for (auto &I: *B) {
            if (I.getType()->isVoidTy()) continue;
            for (auto UIt = I.user_begin(), UE = I.user_end(); UIt != UE; ++UIt) {
                auto *User = dyn_cast<Instruction>(*UIt);
                if (!User) continue;
                auto *UserBlock = User->getParent();
                if (!SL->contains(UserBlock))
                    EscapedRegisters.insert(User);
            }
        }
    }

    for (auto &I: *SL->getHeader()) {
        auto *Phi = dyn_cast<PHINode>(&I);
        if (!Phi) break;
        for (auto K = 0; K < Phi->getNumIncomingValues(); ++K) {
            auto *IncomingBlock = Phi->getIncomingBlock(K);
            auto *IncomingValue = dyn_cast<Instruction>(Phi->getIncomingValue(K));
            if (IncomingValue && IncomingBlock == SL->getLatch() && SL->contains(IncomingValue->getParent())) {
                EscapedRegisters.insert(IncomingValue);
            }
        }
    }

    for (auto It = SL->exiting_begin(), E = SL->exiting_end(); It != E; ++It) {
        auto *Exiting = *It;
        auto Term = Exiting->getTerminator();
        Value *Cond = nullptr;
        if (isa<BranchInst>(Term) && ((BranchInst *) Term)->isConditional()) {
            Cond = Term->getOperand(0);
        } else if (auto *SW = dyn_cast<SwitchInst>(Term)) {
            Cond = SW->getCondition();
        }
        if (auto *CondInst = dyn_cast_or_null<Instruction>(Cond)) {
            if (SL->contains(CondInst->getParent())) {
                EscapedRegisters.insert(CondInst);
            }
        }
    }
}

LoopSummaryAnalysis::~LoopSummaryAnalysis() {
    delete FSM;
    FSM = nullptr;
}

void LoopSummaryAnalysis::incTripCount() {
    if (FSM) FSM->newState(LoopAnalysisID);
    TripCount++;
}

unsigned LoopSummaryAnalysis::getTripCount() const {
    return TripCount;
}

bool LoopSummaryAnalysis::finish() const {
    if (!FSM || FSM->status() == LoopSummaryStateMachine::LSSM_Fail2Summarize)
        return TripCount > LoopUnrollCount;
    return FSM->status() == LoopSummaryStateMachine::LSSM_Summarized;
}

ExecutionState *LoopSummaryAnalysis::getNextInitialState(ExecutionState *ES) {
    if (FSM && FSM->status() == LoopSummaryStateMachine::LSSM_Fail2Summarize) {
        delete FSM;
        FSM = nullptr;
        return InitialState;
    }
    return ES;
}

void LoopSummaryAnalysis::recordMemoryRevised(AbstractValue *V) {
    if (!FSM || FSM->status() == LoopSummaryStateMachine::LSSM_Fail2Summarize) return;
    RevisedMemoryValues.insert(V);
}

void LoopSummaryAnalysis::recordBytesLoaded(const z3::expr &V) {
    if (!FSM || FSM->status() == LoopSummaryStateMachine::LSSM_Fail2Summarize) return;
    auto *CurrState = FSM->recentNewState();
    assert(CurrState);
    CurrState->update(TripCount, V);
}

void LoopSummaryAnalysis::collect(LoopSummaryAnalysis *NestedLSA, ExecutionState *ES) {
    if (!FSM || FSM->status() == LoopSummaryStateMachine::LSSM_Fail2Summarize) return;

    // memory revised in the nested loop should be merged to the upper level loop
    for (auto *State: *NestedLSA->FSM)
        for (auto &It: State->Iterations)
            for (auto &MemIt: It->MemoryValues)
                recordMemoryRevised(MemIt.first.second);

    // at the end of a nested loop, record registers revised
    assert(!FSM->empty());
    auto *State = FSM->recentNewState();
    assert(State);
    for (auto *B: *NestedLSA->CurrLoop) {
        State->update(B);
        for (auto &I: *B) {
            if (EscapedRegisters.count(&I)) {
                // the original value may be released before the next iteration, hence, we need to clone
                auto *AbsVal = ES->boundValue(&I)->clone();
                State->update(TripCount, &I, AbsVal);
            }
        }
    }

    // fixme collect more info
}

void LoopSummaryAnalysis::collect(BasicBlock *B, ExecutionState *ES, unsigned MergeID) {
    assert(CurrLoop->contains(B));

    if (!FSM || FSM->status() == LoopSummaryStateMachine::LSSM_Fail2Summarize) {
        if (B == CurrLoop->getLatch()) {
            bool ExitingLatch = true;
            for (auto PredIt = pred_begin(B), PredE = pred_end(B); PredIt != PredE; ++PredIt) {
                auto *PredB = *PredIt;
                if (!CurrLoop->containsExiting(PredB)) {
                    ExitingLatch = false;
                    break;
                }
            }
            // After Transform/SimplifyLatch, each latch must be terminated by a direct branch instruction
            // if all predecessors of a latch is an exiting block, the current iteration has covered all blocks
            // in the loop body. Hence, we do not need the extra iteration to find the exiting conditions.
            if (TripCount + 1 > LoopUnrollCount && ExitingLatch) TripCount++;
        }

        // record the current exit state in the last iteration when we use the unrolling mode
        if (!CurrLoop->containsExiting(B)) return;

        auto *Term = B->getTerminator();
        for (unsigned I = 0; I < Term->getNumSuccessors(); ++I) {
            auto *Succ = Term->getSuccessor(I);
            if (CurrLoop->contains(Succ)) continue; // not an exiting edge
            auto It = ExitStateMap.find(std::make_pair(B, I));
            if (It == ExitStateMap.end()) {
                ExitStateMap[{B, I}] = ES->fork(B, I, true);
            } else {
                delete It->second;
                It->second = ES->fork(B, I, true);
            }
        }
        return;
    }

    // step 1: if B is a header, record current pc length
    if (B == CurrLoop->getHeader()) {
        PCIndex = ES->pcLength();
    }

    // step 2: collect results
    assert(!FSM->empty());
    auto *State = FSM->recentNewState();
    assert(State);
    State->update(B);
    State->update(TripCount, MergeID);
    for (auto &I: *B) {
        if (EscapedRegisters.count(&I)) {
            // the original value may be released before the next iteration, hence, we need to clone
            auto *AbsVal = ES->boundValue(&I)->clone();
            State->update(TripCount, &I, AbsVal);
        }
    }
    if (B == CurrLoop->getLatch() || CurrLoop->containsExiting(B)) {
        // collect all memory values revised in the loop
        for (auto *V: RevisedMemoryValues) {
            // the original value may be released before the next iteration, hence, we need to clone
            auto AbsVal = ES->getValue(V, false)->clone();
            State->update(TripCount, B, V, AbsVal);
        }

        auto PC = ES->pc(PCIndex, -1);
        State->update(TripCount, B, PC);
        if (B == CurrLoop->getLatch()) {
            RevisedMemoryValues.clear();
            PCIndex = ES->pcLength();
        }
    }

    // step 3: if B is a latch, we need invoke the summarization procedure
    if (B == CurrLoop->getLatch()) {
        FSM->summarizeRecentNewState();
        if (FSM->status() == LoopSummaryStateMachine::LSSM_Summarized) {
            recoverExitingStates();
        } else if (FSM->status() == LoopSummaryStateMachine::LSSM_Fail2Summarize) {
            // we need reanalyze the loop and recollect the exiting states
            assert(ExitStateMap.empty());
            TripCount = 0;
        }
    }
}

void LoopSummaryAnalysis::recoverExitingStates() {
    assert(FSM);
    assert(!FSM->empty());
    assert(FSM->size() == 1 && "FSM->size() > 1 not supported yet!");
    auto *State = FSM->rootState();
    assert(State);

    LLVM_DEBUG(dbgs() << "************************************\n");
    LLVM_DEBUG(dbgs() << "* recover exiting states\n");
    LLVM_DEBUG(dbgs() << "************************************\n");

    // step 0: recover phi conditions
    for (auto &It: State->Iterations[0]->PhiConditions) {
        auto CondVec = Z3::phi_cond(It.first);
        for (unsigned I = 0; I < CondVec.size(); ++I) {
            z3::expr NewCond = It.second[I];
            CondVec.set(I, NewCond);
        }
    }

    // step 1: recover the states after a complete iteration
    for (auto &It: State->Iterations[0]->RegisterValues) {
        InitialState->boundValue(It.first)->assign(It.second);
    }
    for (auto &It: State->Iterations[0]->MemoryValues) {
        if (It.first.first != CurrLoop->getLatch()) continue;
        InitialState->getValue(It.first.second, true)->assign(It.second);
    }
    // recover the pc
    InitialState->addPC(State->Iterations[0]->PathConditions.at(CurrLoop->getLatch()));
    LLVM_DEBUG(dbgs() << *InitialState << "\n");

    // step 2: one extra iteration to get exiting states
    auto From = Z3::vec();
    auto To = Z3::vec();
    if (!State->Iterations[0]->MinIndex.is_bool()) {
        From.push_back(State->Iterations[0]->MinIndex);
        To.push_back(State->Iterations[0]->MaxIndex);
    }
    auto SummarizedTripCount = State->Iterations[0]->TripCount;
    auto NextSummarizedTripCount = Z3::add(SummarizedTripCount, 1);
    From.push_back(SummarizedTripCount);
    To.push_back(NextSummarizedTripCount);

    //   2.1. for registers, just increase the trip count
    for (auto &It: State->Iterations[0]->RegisterValues) {
        auto *AbsV = It.second;
        if (isa<ScalarValue>(AbsV)) {
            auto Val = AbsV->value().substitute(From, To);
            InitialState->boundValue(It.first)->set(Val);
        } else {
            auto Val = AbsV->offset(0).substitute(From, To);
            InitialState->boundValue(It.first)->offset(0) = Val;
        }
    }
    //   2.2. for memory revisions, we need extract memory values at each exiting block
    for (auto ExitingIt = CurrLoop->exiting_begin(), E = CurrLoop->exiting_end(); ExitingIt != E; ++ExitingIt) {
        auto *Exiting = *ExitingIt;
        if (!State->Path.count(Exiting)) continue; // the exiting is not in the state
        auto ExitingState = InitialState->fork();

        for (auto &It: State->Iterations[0]->MemoryValues) {
            if (It.first.first != Exiting) continue;
            auto *AbsV = It.second;
            if (isa<ScalarValue>(AbsV)) {
                auto ExitingAbsV = ExitingState->getValue(It.first.second, true);
                auto Val = AbsV->value().substitute(From, To);
                ExitingAbsV->set(Val);
            } else {
                auto ExitingAbsV = ExitingState->getValue(It.first.second, true);
                ExitingAbsV->assign(AbsV);
                auto Val = AbsV->offset(0).substitute(From, To);
                ExitingAbsV->offset(0) = Val;
            }
        }
        // recover pc
        auto PC = State->Iterations[0]->PathConditions.at(Exiting);
        PC = PC.substitute(From, To);
        ExitingState->addPC(PC);
        LLVM_DEBUG(dbgs() << *ExitingState << "\n");

        // finally, set the exit states
        auto *Term = Exiting->getTerminator();
        unsigned NumExits = 0;
        for (unsigned K = 0; K < Term->getNumSuccessors(); ++K) {
            auto *Exit = Term->getSuccessor(K);
            if (CurrLoop->contains(Exit)) continue;
            ++NumExits;
        }
        for (unsigned K = 0; K < Term->getNumSuccessors(); ++K) {
            auto *Exit = Term->getSuccessor(K);
            if (CurrLoop->contains(Exit)) continue;
            auto OrigIt = ExitStateMap.find({Exiting, K});
            assert(OrigIt == ExitStateMap.end());
            auto *ExitState = ExitingState;
            if (NumExits > 1) {
                ExitState = ExitState->fork(Exiting, K, true);
            } else {
                ExitState->addPC(ExitState->condition(Exiting, K));
            }
            LLVM_DEBUG(dbgs() << *ExitState << "\n");
            ExitStateMap[{Exiting, K}] = ExitState;
            --NumExits;
        }
    }
    delete InitialState;
}
