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

#include <llvm/Support/Debug.h>
#include "Core/LoopSummaryState.h"
#include "Support/Debug.h"

#define DEBUG_TYPE "LoopSummaryState"

LoopSummaryState::~LoopSummaryState() = default;

static LoopIterationRef &recentIteration(unsigned TripCount, std::vector<LoopIterationRef> &Iterations) {
    if (Iterations.empty()) {
        Iterations.emplace_back(std::make_shared<LoopIteration>(TripCount));
    } else {
        auto BackTrip = Iterations.back()->TripCount;
        uint64_t Const;
        if (!Z3::is_numeral_u64(BackTrip, Const) || Const != TripCount) {
            Iterations.emplace_back(std::make_shared<LoopIteration>(TripCount));
        }
    }
    return Iterations.back();
}

void LoopSummaryState::update(unsigned TripCount, Instruction *Val, AbstractValue *AbsVal) {
    recentIteration(TripCount, Iterations)->RegisterValues[Val] = AbsVal;
}

void LoopSummaryState::update(unsigned TripCount, BasicBlock *Block, AbstractValue *Val, AbstractValue *AbsVal) {
    recentIteration(TripCount, Iterations)->MemoryValues[{Block, Val}] = AbsVal;
}

void LoopSummaryState::update(unsigned TripCount, BasicBlock *Block, const z3::expr &PC) {
    recentIteration(TripCount, Iterations)->PathConditions.insert(std::make_pair(Block, PC));
}

void LoopSummaryState::update(unsigned TripCount, const z3::expr &ByteLoaded) {
    recentIteration(TripCount, Iterations)->LoadedBytes.insert(ByteLoaded);
}

void LoopSummaryState::update(unsigned TripCount, unsigned MergeID) {
    if (MergeID < MinMergeID) MinMergeID = MergeID;
    if (MergeID > MaxMergeID) MaxMergeID = MergeID;

    if (MinMergeID == MaxMergeID) {
        // the first time, we call this function
        // MergeID is not actually used
    } else {
        auto Vec = Z3::vec();
        for (auto C: Z3::phi_cond(MergeID)) Vec.push_back(C);
        recentIteration(TripCount, Iterations)->PhiConditions.insert(std::make_pair(MergeID, Vec));
    }
}

void LoopSummaryState::update(BasicBlock *Block) {
    Path.insert(Block);
}

LoopSummaryState *operator^(const LoopSummaryState &S1, const LoopSummaryState &S2) {
    // todo updated revised values in Ret
    assert(S1.CurrLoop == S2.CurrLoop);
    LoopSummaryState *Ret = new LoopSummaryState(S1.CurrLoop, S1.LoopAnalysisID);
    std::vector<BasicBlock *> DFSStack;
    DFSStack.push_back(S1.CurrLoop->getHeader());
    while (!DFSStack.empty()) {
        auto *Top = DFSStack.back();
        DFSStack.pop_back();
        if (Ret->Path.count(Top)) continue;
        Ret->update(Top);
        if (Top == S1.CurrLoop->getLatch())
            break;

        for (auto It = succ_begin(Top), E = succ_end(Top); It != E; ++It) {
            auto *Succ = *It;
            if (S1.Path.count(Succ) && S2.Path.count(Succ))
                DFSStack.push_back(Succ);
        }
    }
    if (Ret->Path.count(S1.CurrLoop->getLatch())) {
        return Ret;
    }
    delete Ret;
    return nullptr;
}

LoopSummaryState *operator-(const LoopSummaryState &S1, const LoopSummaryState &S2) {
    assert(S1.CurrLoop == S2.CurrLoop);
    assert(S2 < S1);
    // todo updated revised values in Ret
    auto *CurrLoop = S1.CurrLoop;
    LoopSummaryState *Ret = new LoopSummaryState(S1.CurrLoop, S1.LoopAnalysisID);
    std::vector<BasicBlock *> DFSStack;
    DFSStack.push_back(S1.CurrLoop->getHeader());
    while (!DFSStack.empty()) {
        auto *Top = DFSStack.back();
        DFSStack.pop_back();
        if (Ret->Path.count(Top)) continue;
        Ret->update(Top);
        if (Top == S1.CurrLoop->getLatch())
            break;

        bool AllSuccInBoth = true;
        for (auto It = succ_begin(Top), E = succ_end(Top); It != E; ++It) {
            auto *Succ = *It;
            if (!CurrLoop->contains(Succ)) continue;
            if (!S1.Path.count(Succ) || !S2.Path.count(Succ)) {
                AllSuccInBoth = false;
                break;
            }
        }
        if (AllSuccInBoth) {
            // the successors of this block does not distinguish the two states
            for (auto It = succ_begin(Top), E = succ_end(Top); It != E; ++It) {
                auto *Succ = *It;
                if (!CurrLoop->contains(Succ)) continue;
                DFSStack.push_back(Succ);
            }
        } else {
            // the successors of this block distinguishes the two states
            for (auto It = succ_begin(Top), E = succ_end(Top); It != E; ++It) {
                auto *Succ = *It;
                if (!CurrLoop->contains(Succ)) continue;
                if (S1.Path.count(Succ) && !S2.Path.count(Succ))
                    DFSStack.push_back(Succ);
            }
        }
    }
    assert(S1.Path.count(S1.CurrLoop->getHeader()));
    assert(S1.Path.count(S1.CurrLoop->getLatch()));
    return Ret;
}

bool operator<(const LoopSummaryState &S1, const LoopSummaryState &S2) {
    assert(S1.CurrLoop == S2.CurrLoop);
    if (S1.Path.size() >= S2.Path.size())
        return false;

    std::set<BasicBlock *> Intersection;
    std::set_intersection(S1.Path.begin(), S1.Path.end(),
                          S2.Path.begin(), S2.Path.end(),
                          std::inserter(Intersection, Intersection.begin()));
    return Intersection == S1.Path;
}

bool operator>(const LoopSummaryState &S1, const LoopSummaryState &S2) {
    return S2 < S1;
}

bool operator==(const LoopSummaryState &S1, const LoopSummaryState &S2) {
    assert(S1.CurrLoop == S2.CurrLoop);
    return S1.Path == S2.Path;
}

raw_ostream &operator<<(llvm::raw_ostream &O, const LoopSummaryState &State) {
    if (State.Iterations.empty()) {
        O << "empty iterations!";
        return O;
    }

    std::string Str;
    raw_string_ostream StrO(Str);

    auto &FirstIteration = State.Iterations[0];
    for (auto &It: FirstIteration->RegisterValues) {
        StrO << *It.first;
        StrO.flush();
        O << StringRef(Str).trim() << "\n";
        Str.clear();

        O << "\t" << FirstIteration->TripCount << " >> " << It.second->str() << "\n";
        for (unsigned K = 1; K < State.Iterations.size(); ++K) {
            auto &NextIteration = State.Iterations[K];
            auto KIt = NextIteration->RegisterValues.find(It.first);
            if (KIt != NextIteration->RegisterValues.end()) {
                O << "\t" << NextIteration->TripCount << " >> " << KIt->second->str() << "\n";
            } else {
                O << "\t" << NextIteration->TripCount << " >> n/a\n";
            }
        }
        O << "--------------------\n";
    }

    for (auto &It: FirstIteration->MemoryValues) {
        O << It.first.first->getName() << ", " << It.first.second->str() << "\n";
        O << "\t" << FirstIteration->TripCount << " >> " << It.second->str() << "\n";

        for (unsigned K = 1; K < State.Iterations.size(); ++K) {
            auto &NextIteration = State.Iterations[K];
            auto KIt = NextIteration->MemoryValues.find(It.first);
            if (KIt != NextIteration->MemoryValues.end()) {
                O << "\t" << NextIteration->TripCount << " >> " << KIt->second->str() << "\n";
            } else {
                O << "\t" << NextIteration->TripCount << " >> n/a\n";
            }
        }
        O << "--------------------\n";
    }

    for (auto &It: FirstIteration->PathConditions) {
        O << "pc @ " << It.first->getName() << "\n";
        O << "\t" << FirstIteration->TripCount << " >> " << It.second << "\n";

        for (unsigned K = 1; K < State.Iterations.size(); ++K) {
            auto &NextIteration = State.Iterations[K];
            auto KIt = NextIteration->PathConditions.find(It.first);
            if (KIt != NextIteration->PathConditions.end()) {
                O << "\t" << NextIteration->TripCount << " >> " << KIt->second << "\n";
            } else {
                O << "\t" << NextIteration->TripCount << " >> n/a\n";
            }
        }
        O << "--------------------\n";
    }

    O << "bytes loaded\n";
    for (auto &Iteration: State.Iterations) {
        O << "\t" << Iteration->TripCount << " >> ";
        for (auto Byte: Iteration->LoadedBytes) {
            O << Byte << ", ";
        }
        O << "\n";
    }
    O << "----------------------\n";
    return O;
}

unsigned LoopSummaryState::summarize(LoopSummaryState *State) {
    if (Iterations.size() == 1 && !Iterations[0]->TripCount.is_numeral()) {
        // this is a summarized state, check if the new input State follows the summarized state. it should be.
        return 2;
    } else {
        assert(State->Iterations.size() == 1);
        Iterations.push_back(State->Iterations[0]);
        LLVM_DEBUG(dbgs() << *this << "\n");
        if (Iterations.size() > 2) {
            // if there are enough concrete states to summarize, then summarize
            try {
                summarize();
                return 1;
            } catch (const std::runtime_error &Exception) {
                StringRef ErrMsg(Exception.what());
                SmallVector<StringRef, 5> SplitMsgVec;
                ErrMsg.split(SplitMsgVec, '\n', -1, false);
                for (auto &Msg: SplitMsgVec)
                    pardiff_WARN("[Loop] " << Msg);
                return 3;
            }
        } else {
            // if there are not enough concrete states to summarize, then just collect the results
            return 0;
        }
    }
}

static unsigned complexity(const z3::expr &E) {
    assert(E.is_bv());
    auto Vec = Z3::find_consecutive_ops(E, Z3_OP_BADD, true);
    unsigned Size = 0;
    for (auto V: Vec) {
        if (Z3::is_phi(V)) {
            unsigned MaxSize = 0;
            for (unsigned K = 0; K < V.num_args(); ++K) {
                auto S = complexity(V.arg(K));
                if (S > MaxSize) MaxSize = S;
            }
            Size += MaxSize;
        } else {
            Size++;
        }
    }
    return Size;
}

static z3::expr substitute_byte(const z3::expr &E, const z3::expr &F, const z3::expr &T) {
    if (E.decl().decl_kind() == Z3_OP_SELECT) {
        if (Z3::same(E, F)) {
            return T;
        } else {
            return E;
        }
    } else {
        auto Vec = Z3::vec();
        for (unsigned K = 0; K < E.num_args(); ++K) {
            auto FB = F;
            auto TB = T;
            if (Z3::is_phi(E)) {
                FB = Z3::select_phi_arg(Z3::phi_id(E), K, F);
            }
            auto RetK = substitute_byte(E.arg(K), FB, TB);
            Vec.push_back(RetK);
        }
        return E.decl()(Vec);
    }
}

static z3::expr decompose_bool_phi(const z3::expr &E) {
    if (!Z3::is_phi(E) || !E.is_bool()) return E;

    auto FirstDecl = E.arg(0).decl();
    for (unsigned K = 1; K < E.num_args(); ++K) {
        assert(FirstDecl.id() == E.arg(K).decl().id());
    }

    auto DecomposedExpr = E;
    if (Z3::is_phi(E.arg(0))) { // nested phi
        auto Vec = Z3::vec();
        for (unsigned K = 0; K < E.num_args(); ++K) {
            Vec.push_back(decompose_bool_phi(E.arg(K)));
        }
        DecomposedExpr = E.decl()(Vec);
        assert(!Z3::is_phi(DecomposedExpr.arg(0)));
        DecomposedExpr = decompose_bool_phi(DecomposedExpr);
    } else {
        auto DeclArgNum = FirstDecl.arity();
        auto Vec = Z3::vec();
        for (unsigned I = 0; I < DeclArgNum; ++I) {
            auto PhiVec = Z3::vec();
            for (unsigned K = 0; K < E.num_args(); ++K) {
                PhiVec.push_back(E.arg(K).arg(I));
            }
            Vec.push_back(Z3::make_phi(Z3::phi_id(E), PhiVec));
        }
        DecomposedExpr = FirstDecl(Vec);
    }
    return DecomposedExpr;
}

static z3::expr substitute_exp(const z3::expr &E, const z3::expr &F, const z3::expr &T) {
    if (E.is_bool()) {
        if (E.is_and() || E.is_or() || E.is_not() || Z3::is_compare(E)) {
            auto Vec = Z3::vec();
            for (unsigned K = 0; K < E.num_args(); ++K) {
                Vec.push_back(substitute_exp(E.arg(K), F, T));
            }
            return E.decl()(Vec);
        } else if (Z3::is_phi(E)) {
            auto DecomposedPhi = decompose_bool_phi(E);
            return substitute_exp(DecomposedPhi, F, T);
        } else if (E.is_const()) {
            return E;
        } else {
            errs() << E << "\n";
            llvm_unreachable("Error: unknown bool type expr!");
        }
    } else if (E.is_const()) {
        return E;
    } else {
        assert(E.is_bv());
        auto Expr = E;
        if (E.get_sort().bv_size() == F.get_sort().bv_size()) {
            Expr = Z3::sub(Z3::add(E, F), T);
            if (complexity(Expr) > complexity(E)) {
                Expr = Z3::sub(Z3::add(E, T), F);
                if (complexity(Expr) > complexity(E)) {
                    Expr = E;
                }
            }
        }
        return Expr;
    }
}

static z3::expr substitute(const z3::expr &E, const z3::expr_vector &F, const z3::expr_vector &T) {
    auto Ret = E;
    for (unsigned K = 0; K < F.size(); ++K) {
        auto FK = F[K], TK = T[K];
        if (FK.decl().decl_kind() == Z3_OP_SELECT && TK.decl().decl_kind() == Z3_OP_SELECT) {
            Ret = substitute_byte(Ret, FK, TK);
        } else {
            Ret = substitute_exp(Ret, FK, TK);
        }
    }
    LLVM_DEBUG(dbgs() << "... substitution: " << E << "\n");
    LLVM_DEBUG(dbgs() << "substitution ...: " << Ret << "\n");
    LLVM_DEBUG(dbgs() << "..................................\n");
    return Ret;
}

void LoopSummaryState::summarizeBase() {
    // step 1: if all byte indices are constant, we do not need to summarize the base index
    {
        bool NeedSummarizeBase = false;
        for (auto It: Iterations) {
            for (auto E: It->LoadedBytes) {
                assert(E.decl().decl_kind() == Z3_OP_SELECT);
                if (!E.arg(1).is_numeral()) {
                    NeedSummarizeBase = true;
                    break;
                }
            }
        }
        if (!NeedSummarizeBase) return;
    }

    // step 2: remove all shared bytes across different iterations
    {
        std::vector<std::set<z3::expr, Z3::less_than> *> ToRelease;
        std::set<z3::expr, Z3::less_than> *CommonBytes = new std::set<z3::expr, Z3::less_than>;
        ToRelease.push_back(CommonBytes);
        std::set<z3::expr, Z3::less_than> *WorkingBytes = &Iterations[0]->LoadedBytes;
        for (unsigned K = 1; K < Iterations.size();) {
            auto &NextLoadedByteSet = Iterations[K]->LoadedBytes;
            std::set_intersection(WorkingBytes->begin(), WorkingBytes->end(),
                                  NextLoadedByteSet.begin(), NextLoadedByteSet.end(),
                                  std::inserter(*CommonBytes, CommonBytes->begin()));
            if (++K < Iterations.size()) {
                WorkingBytes = CommonBytes;
                CommonBytes = new std::set<z3::expr, Z3::less_than>;
                ToRelease.push_back(CommonBytes);
            }
        }
        bool AllEmpty = true;
        bool SameSize = true;
        for (unsigned K = 0; K < Iterations.size(); ++K) {
            auto &LoadedBytes = Iterations[K]->LoadedBytes;
            for (auto E: *CommonBytes) LoadedBytes.erase(E);
            if (AllEmpty && !LoadedBytes.empty()) AllEmpty = false;
            if (SameSize && K > 0 && LoadedBytes.size() != Iterations[K - 1]->LoadedBytes.size()) SameSize = false;
        }
        for (auto *S: ToRelease) delete S;
        if (!SameSize) throw std::runtime_error("Loop cannot be summarized due to different number of loaded bytes.");
        if (AllEmpty) return; // no need to summarize
    }

    // step 3: for each iteration, find the min/max indices
    for (auto It: Iterations) {
        for (auto Byte: It->LoadedBytes) {
            assert(Byte.decl().decl_kind() == Z3_OP_SELECT);
            if (It->MinIndex.is_bool()) {
                It->MinIndex = Byte.arg(1);
                It->MaxIndex = Byte.arg(1);
            } else if (Z3::byte_array_element_index_less_than(Byte.arg(1), It->MinIndex)) {
                It->MinIndex = Byte.arg(1);
            } else {
                It->MaxIndex = Byte.arg(1);
            }
        }
    }

    auto Base = Z3::base(LoopAnalysisID);
    for (unsigned K = 0; K < Iterations.size(); ++K) {
        auto It = Iterations[K];
        auto From = Z3::vec();
        auto To = Z3::vec();

        for (auto Byte: It->LoadedBytes) {
            assert(Byte.decl().decl_kind() == Z3_OP_SELECT);
            From.push_back(Byte);
            To.push_back(Z3::byte_array_element(Byte.arg(0), Z3::add(Base, Z3::sub(Byte.arg(1), It->MinIndex))));
        }
        for (unsigned J = 0; J < 4; ++J) {
            if (It->MinIndex.is_numeral()) break;
            unsigned TargetBW = 8 * (1 << (3 - J)); // 64bit - 32bit - 16bit - 8bit
            auto BasePtr = Z3::trunc(Base, TargetBW);
            auto MinPtr = Z3::trunc_expression(It->MinIndex, TargetBW);
            if (MinPtr.get_sort().bv_size() != TargetBW) break;
            From.push_back(MinPtr);
            To.push_back(BasePtr);
        }
        LLVM_DEBUG(dbgs() << "from ! " << It->TripCount << "\n");
        LLVM_DEBUG(for (auto E: From) dbgs() << "\t" << E << "\n");
        LLVM_DEBUG(dbgs() << "to ! " << It->TripCount << "\n");
        LLVM_DEBUG(for (auto E: To) dbgs() << "\t" << E << "\n");

        auto OrigFromToSize = From.size();
        // replace abstract values using the base ptr
        for (auto &RIt: It->RegisterValues) {
            auto *AbsVal = RIt.second;
            if (isa<AddressValue>(AbsVal)) {
                if (AbsVal->size() != 1) continue;
                auto Val = AbsVal->offset(0);
                Val = substitute(Val, From, To);
                AbsVal->offset(0) = Val.simplify();
            } else {
                auto Val = AbsVal->value();
                Val = substitute(Val, From, To);
                AbsVal->set(Val.simplify());
            }
        }
        for (auto &MIt: It->MemoryValues) {
            auto *AbsVal = MIt.second;
            if (isa<AddressValue>(AbsVal)) {
                if (AbsVal->size() != 1) continue;
                auto Val = AbsVal->offset(0);
                Val = substitute(Val, From, To);
                AbsVal->offset(0) = Val.simplify();
            } else {
                auto Val = AbsVal->value();
                Val = substitute(Val, From, To);
                AbsVal->set(Val.simplify());
            }
        }
        for (auto &PCIt: It->PathConditions) {
            PCIt.second = substitute(PCIt.second, From, To);
        }
        for (auto &PhiCondIt: It->PhiConditions) {
            for (unsigned I = 0; I < PhiCondIt.second.size(); ++I) {
                auto Cond = PhiCondIt.second[I];
                Cond = substitute(Cond, From, To);
                PhiCondIt.second.set(I, Cond);
            }
        }

        if (K + 1 < Iterations.size()) {
            auto Span = Z3::sub(Iterations[K + 1]->MinIndex, It->MinIndex);
            Span = substitute(Span, From, To);
            It->MaxIndex = Z3::add(Base, Span);
        }
        It->Sugar = (It->MinIndex == Base);
        It->MinIndex = Base;
        LLVM_DEBUG(dbgs() << "min : " << It->MinIndex << "\n");
        LLVM_DEBUG(dbgs() << "max : " << It->MaxIndex << "\n");
        LLVM_DEBUG(dbgs() << "sug : " << It->Sugar << "\n");
        LLVM_DEBUG(dbgs() << "---------------------\n");
    }
    return;
}

static z3::expr
summarizeConst(const z3::expr &C1, const z3::expr &C2, const z3::expr &C3, const z3::expr &SG, const z3::expr &TC) {
    auto RealC1 = C1;
    if (Z3::same(C1, C2) && Z3::same(C1, C3)) {
        return C1;
    } else {
        auto Delta1 = Z3::sub(C2, C1);
        auto Delta2 = Z3::sub(C3, C2);
        bool SameDelta = Z3::same(Delta1, Delta2);
        if (!SameDelta && SG.is_eq()) {
            unsigned C2BW = C2.get_sort().bv_size();
            auto SG0 = Z3::trunc_expression(SG.arg(0), C2BW);
            auto SG1 = Z3::trunc_expression(SG.arg(1), C2BW);
            // try some alternatives: since SG0 == SG1, we have
            //   Z3::add(C1, Z3::sub(SG0, SG1)) == C1
            //   Z3::add(C1, Z3::sub(SG1, SG0)) == C1
            RealC1 = Z3::add(C1, Z3::sub(SG0, SG1));
            Delta1 = Z3::sub(C2, RealC1);
            SameDelta = Z3::same(Delta1, Delta2);
            if (!SameDelta) {
                RealC1 = Z3::add(C1, Z3::sub(SG1, SG0));
                Delta1 = Z3::sub(C2, RealC1);
                SameDelta = Z3::same(Delta1, Delta2);
            }
        }

        if (!SameDelta) {
            std::string ErrMsg;
            raw_string_ostream Str(ErrMsg);
            Str << "Loop cannot be summarized due to variable delta...\n";
            Str << "\t" << C1 << " ------ " << C2 << " ------ " << C3 << "\n";
            Str << "\t" << Delta1 << " ------vs.------ " << Delta2 << "\n";
            Str.flush();
            throw std::runtime_error(ErrMsg.c_str());
        }

        auto Delta = Delta1;
        auto TripCount = TC;
        if (Z3::is_base(Delta) || (Delta.decl().decl_kind() == Z3_OP_BMUL && Z3::is_base(Delta.arg(1)))) {
            TripCount = Z3::bv_val(1, Delta.get_sort().bv_size());
        } else if (Delta.get_sort().bv_size() > TC.get_sort().bv_size()) {
            TripCount = Z3::zext(TC, Delta.get_sort().bv_size());
        } else if (Delta.get_sort().bv_size() < TC.get_sort().bv_size()) {
            TripCount = Z3::trunc(TC, Delta.get_sort().bv_size());
        }
        auto Value = Z3::add(RealC1, Z3::mul(Delta, TripCount));
        return Value;
    }
}

static z3::expr
summarize(const z3::expr &C1, const z3::expr &C2, const z3::expr &C3, const z3::expr &SG, const z3::expr &TC) {
    auto C1Decl = C1.decl();
    auto C2Decl = C2.decl();
    auto C3Decl = C3.decl();

    if (C1Decl.decl_kind() != C2Decl.decl_kind() || C1Decl.decl_kind() != C3Decl.decl_kind()) {
        return summarizeConst(C1, C2, C3, SG, TC);
    } else if (C1.num_args() != C2.num_args() || C2.num_args() != C3.num_args()) {
        return summarizeConst(C1, C2, C3, SG, TC);
    } else if (C1.num_args() == 0) {
        return summarizeConst(C1, C2, C3, SG, TC);
    } else {
        assert(C1.num_args() == C2.num_args() && C2.num_args() == C3.num_args());
        auto ArgVec = Z3::vec();
        for (unsigned K = 0; K < C1.num_args(); ++K) {
            auto CK = summarize(C1.arg(K), C2.arg(K), C3.arg(K), SG, TC);
            ArgVec.push_back(CK);
        }
        return C1Decl(ArgVec);
    }
}

static void summarize(AbstractValue *V1, AbstractValue *V2, AbstractValue *V3, const z3::expr &SG, const z3::expr &TC) {
    assert(V1);
    if (!V1 || !V2 || !V3) {
        V1->mkpoison();
        return;
    }
    if (V1->poison() || V2->poison() || V3->poison()) {
        V1->mkpoison();
        return;
    }
    if (isa<AddressValue>(V1)) {
        if (V1->size() != 1 || V2->size() != 1 || V3->size() != 1) {
            V1->mkpoison();
            return;
        }
    }

    auto E1 = isa<AddressValue>(V1) ? V1->offset(0) : V1->value();
    auto E2 = isa<AddressValue>(V1) ? V2->offset(0) : V2->value();
    auto E3 = isa<AddressValue>(V1) ? V3->offset(0) : V3->value();

    auto E = summarize(E1, E2, E3, SG, TC);
    if (isa<AddressValue>(V1)) V1->offset(0) = E;
    else V1->value() = E;
}

void LoopSummaryState::summarizeTrip() {
    assert(Iterations.size() == 3);

    auto TripCount = Z3::trip_count(LoopAnalysisID);
    auto FirstIteration = Iterations[0];
    auto Sugar = FirstIteration->Sugar;

    for (auto &It: FirstIteration->RegisterValues) {
        auto *Reg = It.first;
        auto *Val0 = It.second;
        if (Val0->poison()) continue;
        auto Val1 = Iterations[1]->reg(Reg);
        auto Val2 = Iterations[2]->reg(Reg);
        LLVM_DEBUG(dbgs() << "summarize reg val: \n");
        LLVM_DEBUG(dbgs() << "\t " << Val0->str() << "\n");
        LLVM_DEBUG(dbgs() << "\t " << Val1->str() << "\n");
        LLVM_DEBUG(dbgs() << "\t " << Val2->str() << "\n");
        ::summarize(Val0, Val1, Val2, Sugar, TripCount);
    }

    for (auto &It: FirstIteration->MemoryValues) {
        auto &Reg = It.first;
        auto *Val0 = It.second;
        if (Val0->poison()) continue;
        auto Val1 = Iterations[1]->mem(Reg);
        auto Val2 = Iterations[2]->mem(Reg);
        LLVM_DEBUG(dbgs() << "summarize mem val: \n");
        LLVM_DEBUG(dbgs() << "\t " << Val0->str() << "\n");
        LLVM_DEBUG(dbgs() << "\t " << Val1->str() << "\n");
        LLVM_DEBUG(dbgs() << "\t " << Val2->str() << "\n");
        ::summarize(Val0, Val1, Val2, Sugar, TripCount);
    }

    for (auto &It: FirstIteration->PathConditions) {
        auto Blk = It.first;
        auto PC0 = It.second;
        auto PC1 = Iterations[1]->pc(Blk);
        auto PC2 = Iterations[2]->pc(Blk);
        LLVM_DEBUG(dbgs() << "summarize pc: \n");
        LLVM_DEBUG(dbgs() << "\t " << PC0 << "\n");
        LLVM_DEBUG(dbgs() << "\t " << PC1 << "\n");
        LLVM_DEBUG(dbgs() << "\t " << PC2 << "\n");
        auto NewPC = ::summarize(PC0, PC1, PC2, Sugar, TripCount);
        It.second = NewPC;
    }

    for (auto &It: FirstIteration->PhiConditions) {
        unsigned PhiID = It.first;
        auto CondVec0 = It.second;
        auto CondVec1 = Iterations[1]->phi(PhiID);
        auto CondVec2 = Iterations[2]->phi(PhiID);
        assert(CondVec0.size() == CondVec1.size() && CondVec0.size() == CondVec2.size());
        for (unsigned K = 0; K < CondVec0.size(); ++K) {
            auto CondK0 = CondVec0[K];
            auto CondK1 = CondVec1[K];
            auto CondK2 = CondVec2[K];
            LLVM_DEBUG(dbgs() << "summarize phi cond: \n");
            LLVM_DEBUG(dbgs() << "\t " << CondK0 << "\n");
            LLVM_DEBUG(dbgs() << "\t " << CondK1 << "\n");
            LLVM_DEBUG(dbgs() << "\t " << CondK2 << "\n");
            auto NewCond = ::summarize(CondK0, CondK1, CondK2, Sugar, TripCount);
            It.second.set(K, NewCond);
        }
    }

    // after summarization, set trip count to K
    FirstIteration->TripCount = TripCount;

    // after summarization, delete useless concrete values
    while (Iterations.size() > 1) Iterations.pop_back();
}

void LoopSummaryState::summarize() {
    assert(Iterations.size() > 2);
    LLVM_DEBUG(dbgs() << *this << "\n");

    // step 1. summarize using a base index
    summarizeBase();
    LLVM_DEBUG(dbgs() << *this << "\n");

    // step 2. summarize using a variable trip count
    summarizeTrip();
    LLVM_DEBUG(dbgs() << *this << "\n");
    LLVM_DEBUG(dbgs() << "");
}
