/*
 *  pardiff lifts protocol source code in C to its specification in BNF
 *  Copyright (C) 2021  
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

#include <llvm/IR/Constants.h>
#include <llvm/IR/GlobalAlias.h>
#include <llvm/IR/GlobalIFunc.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/Instructions.h>
#include <llvm/Support/ManagedStatic.h>

#include "Core/ExecutionState.h"
#include "Support/PushPop.h"

using namespace llvm;

typedef std::map<Value *, std::shared_ptr<AbstractValue>> RegisterSpace;

static ManagedStatic<RegisterSpace> RegisterMem; // constant memory space
static MessageBuffer *MessageMem = nullptr; // constant memory space
static std::vector<GlobalMemoryBlock *> GlobalMem; // constant memory space, we only handle constant global now
static std::vector<HeapMemoryBlock *> HeapMem; // variable memory space
static PushPopVector<StackMemoryBlock *> StackMem; // variable memory space

ExecutionState::ExecutionState() = default;

ExecutionState::~ExecutionState() = default;

ExecutionState *ExecutionState::fork(BasicBlock *B, unsigned I, bool LoopExiting) {
    z3::expr Cond = condition(B, I);
//    if (Z3::to_string(Cond).find("-1 x 0") != std::string::npos) {
//        outs() << "";
//    }
    if (!LoopExiting && conflict(Cond))
        return nullptr;

    auto *Ret = new ExecutionState(*this);
#ifndef NDEBUG
    Ret->ForkBlock = B;
    Ret->ForkBlockBr = I;
#endif
    if (!Z3::is_free(Cond) && !Cond.is_true() && !Cond.is_false()) {
        Ret->PC.push_back(Cond);
    }
    return Ret;
}

ExecutionState *ExecutionState::fork() {
    auto *Ret = new ExecutionState(*this);
    return Ret;
}

static void merge(std::map<BasicBlock *, std::set<unsigned>> &Dst, std::map<BasicBlock *, std::set<unsigned>> &Src) {
    for (auto &It: Src) {
        auto *Block = It.first;
        auto &Vec = It.second;

        auto DstIt = Dst.find(Block);
        if (DstIt == Dst.end()) {
            Dst.insert(It);
        } else {
            DstIt->second.insert(Vec.begin(), Vec.end());
        }
    }

    auto It = Dst.begin();
    while (It != Dst.end()) {
        if (It->first->getTerminator()->getNumSuccessors() == It->second.size()) {
            It = Dst.erase(It);
        } else {
            ++It;
        }
    }
}

void ExecutionState::merge(
        unsigned MergeID,
        const std::map<AbstractValue *, std::vector<std::pair<AbstractValue *, unsigned>>> &MergeMap,
        const std::vector<z3::expr> &MergeCond) {
    // merge revised abstract values
    auto AllSame = [&MergeCond](const std::vector<std::pair<AbstractValue *, unsigned>> &Vec) {
        for (unsigned I = 0; I < Vec.size(); ++I) {
            AbstractValue *First = 0;
            if (!MergeCond[Vec[I].second].is_false()) {
                First = Vec[I].first;
            } else {
                continue;
            }
            assert(I == 0);
            for (unsigned J = I + 1; J < Vec.size(); ++J) {
                if (!MergeCond[Vec[J].second].is_false() && First != Vec[J].first) {
                    return false;
                }
            }
            break;
        }
        return true;
    };

    for (auto &It: MergeMap) {
        auto Key = It.first;
        auto &ValVec = It.second;
        assert(!ValVec.empty());
        if (AllSame(ValVec)) {
            getValue(Key, true)->assign(ValVec[0].first);
        } else {
            auto NewAbsVal = getValue(Key, true);
            if (isa<ScalarValue>(ValVec[0].first)) {
                auto PhiVec = Z3::vec();
                auto CondVec = Z3::vec();
                for (auto &Pair: ValVec) {
                    auto PairFirst = Pair.first;
                    if (PairFirst->poison()) PhiVec.push_back(Z3::free_bv(PairFirst->bytewidth() * 8));
                    else PhiVec.push_back(PairFirst->value());
                    CondVec.push_back(MergeCond[Pair.second]);
                }

                NewAbsVal->set(Z3::make_phi(MergeID, PhiVec, CondVec));
            } else {
                std::vector<std::pair<AddressValue *, z3::expr>> AddressPhiVec;
                for (auto &Pair: ValVec) {
                    AddressPhiVec.emplace_back((AddressValue *) Pair.first, MergeCond[Pair.second]);
                }

                if (!optimize(AddressPhiVec)) {
                    auto Ret = optimize2(AddressPhiVec, MergeID);
                    if (Ret.get()) {
                        NewAbsVal->assign(Ret.get());
                        AddressPhiVec.clear();
                    }
                }
                for (auto &X: AddressPhiVec) {
                    NewAbsVal->add(X.first);
                }
            }
        }
    }
}

static unsigned subset(std::vector<z3::expr> &V1, std::vector<z3::expr> &V2) {
    // return 1 if V1 < V2
    // return -1 if V1 > V2
    // return 0 if V1 = V2
    // return 2 otherwise
    unsigned K = 0;
    for (; K < V1.size() && K < V2.size(); ++K) {
        if (!Z3::same(V1[K], V2[K])) {
            break;
        }
    }
    if (K == V1.size()) {
        if (K == V2.size()) {
            return 0;
        } else {
            // V1 < V2
            return 1;
        }
    } else if (K == V2.size()) {
        // V1 > V2
        return -1;
    }
    return 2;
}

void ExecutionState::merge(BasicBlock *B, unsigned MergeID, std::vector<ExecutionState *> &ESVec,
                           std::vector<z3::expr> &MergeCond) {
    // remove A if A's pc is a subsequence of the other B's pc
    auto *MergeFlagVec = new unsigned[ESVec.size()];
    for (unsigned I = 0; I < ESVec.size(); ++I) {
        if (!ESVec[I] || (ESVec[I]->PC.size() == 1 && ESVec[I]->PC[0].is_false())) {
            MergeFlagVec[I] = UINT_MAX;
        } else {
            MergeFlagVec[I] = I;
        }
    }
    for (unsigned I = 0; I < ESVec.size(); ++I) {
        if (MergeFlagVec[I] == UINT_MAX) continue;
        auto &CurrPCVec = ESVec[I]->PC;
        for (unsigned J = I + 1; J < ESVec.size(); ++J) {
            if (MergeFlagVec[J] == UINT_MAX) continue;
            auto &NextPCVec = ESVec[J]->PC;
            unsigned SubSet = ::subset(CurrPCVec, NextPCVec);
            if (SubSet == -1) { // CurrPCVec > NextPCVec
                for (unsigned K = 0; K < ESVec.size(); ++K) {
                    if (MergeFlagVec[J] == MergeFlagVec[K]) MergeFlagVec[K] = UINT_MAX;
                }
            } else if (SubSet == 0) {
                MergeFlagVec[J] = MergeFlagVec[I];
            } else if (SubSet == 1) {
                for (unsigned K = 0; K < ESVec.size(); ++K) {
                    if (MergeFlagVec[I] == MergeFlagVec[K]) MergeFlagVec[K] = UINT_MAX;
                }
                break;
            }
        }
    }

    // merge pc by extracting the common prefix
    for (unsigned I = 0; I < ESVec.size(); ++I) {
        if (MergeFlagVec[I] == UINT_MAX) continue;

        ExecutionState *FirstES = ESVec[I];
        unsigned CommonPrefixLen = 0;
        while (CommonPrefixLen < FirstES->PC.size()) {
            bool AllSame = true;
            for (unsigned J = I + 1; J < ESVec.size(); ++J) {
                if (MergeFlagVec[J] == UINT_MAX) continue;

                auto *ES = ESVec[J];
                if (CommonPrefixLen < ES->PC.size()
                    && CommonPrefixLen < FirstES->PC.size()
                    && Z3::same(ES->PC[CommonPrefixLen], FirstES->PC[CommonPrefixLen])) {
                } else {
                    AllSame = false;
                    break;
                }
            }
            if (AllSame) PC.push_back(FirstES->PC[CommonPrefixLen++]);
            else break;
        }
        assert(CommonPrefixLen == PC.size());
        break;
    }
    std::vector<z3::expr> AndVec;
    for (unsigned I = 0; I < ESVec.size(); ++I) {
        if (MergeFlagVec[I] == UINT_MAX) {
            MergeCond.push_back(Z3::bool_val(false));
            continue;
        }
        AndVec.clear();
        auto *CurrES = ESVec[I];
        for (unsigned J = PC.size(); J < CurrES->PC.size(); ++J) {
            AndVec.push_back(CurrES->PC[J]);
        }
        MergeCond.push_back(Z3::make_and(AndVec));
    }
    // postprocessing the merge conditions, we can simplify the merge condition as below
    //  e.g., phi(v, c && !c, ...) => phi(v, false, ...)
    //
    // but we cannot simplify the merge condition aggressively
    //  e.g., phi(v, c || !c, ...) => phi(v, true, ...)
    //   the former means that, at a path with a condition, c or !c, use v;
    //   the latter means that in any condition, use v
    z3::expr_vector MergeCondZ3Vec = Z3::vec(); // < for compute the pc, but preserve the structure of phi cond
    std::set<unsigned> PushedMergeCondSet;
    for (unsigned I = 0; I < MergeCond.size(); ++I) {
        auto Cond = MergeCond[I];
        auto Simplified = Cond.simplify();
        if (Simplified.is_false()) {
            MergeCond[I] = Simplified;
        } else if (!PushedMergeCondSet.count(Z3::id(Cond))) {
            MergeCondZ3Vec.push_back(Cond);
            PushedMergeCondSet.insert(Z3::id(Cond));
        }
    }

    // to merge memory values from different states
    std::map<AbstractValue *, std::vector<std::pair<AbstractValue *, unsigned>>> MergeMap;
    for (unsigned I = 0; I < ESVec.size(); ++I) {
        if (MergeCond[I].is_false()) continue;
        auto *ES = ESVec[I];
        assert(ES);
        for (auto &It: ES->AbsValRevisionMap) {
            MergeMap[It.first]; //.emplace_back(It.second, I);
        }
    }
    for (auto &It: MergeMap) {
        for (unsigned I = 0; I < ESVec.size(); ++I) {
            if (MergeCond[I].is_false()) continue;
            auto *ES = ESVec[I];
            assert(ES);
            It.second.emplace_back(ES->getValue(It.first, false), I);
        }
    }
    merge(MergeID, MergeMap, MergeCond);

    // to merge named byte sets, just compute the set intersection
    std::set<unsigned> IntersectionResults;
    std::set<unsigned> *FirstSet = nullptr;
    for (unsigned I = 0; I < ESVec.size(); ++I) {
        if (MergeCond[I].is_false()) continue;
        auto *ES = ESVec[I];
        assert(ES);
        if (!FirstSet) {
            NamedByteSet = ES->NamedByteSet;
            FirstSet = &NamedByteSet;
        } else {
            auto &CurrSet = ES->NamedByteSet;
            std::set_intersection(FirstSet->begin(), FirstSet->end(),
                                  CurrSet.begin(), CurrSet.end(),
                                  std::inserter(IntersectionResults, IntersectionResults.end()));
            NamedByteSet = std::move(IntersectionResults);
        }
    }

    // compute pc
    // it is guaranteed that no false and no duplicates in MergeCondZ3Vec
    // we need to use z3's original mk_or to preserve the cond structure of phi
    assert(!MergeCondZ3Vec.empty());
    if (MergeCondZ3Vec.size() == 1) {
        auto NewPCExpr = MergeCondZ3Vec[0].simplify();
        assert(!NewPCExpr.is_false());
        if (!NewPCExpr.is_true() && !Z3::is_free(NewPCExpr))
            PC.push_back(NewPCExpr);
    } else {
        if (!Z3::has_phi(MergeID) && !isa<PHINode>(*B->begin())) {
            // if no phi generated, we can use Z3::make_or
            auto NewPCExpr = Z3::make_or(MergeCondZ3Vec);
            assert(!NewPCExpr.is_false());
            if (!NewPCExpr.is_true() && !Z3::is_free(NewPCExpr)) PC.push_back(NewPCExpr);
        } else {
            auto NewPCExpr = z3::mk_or(MergeCondZ3Vec);
            if (!NewPCExpr.is_true() && !Z3::is_free(NewPCExpr)) PC.push_back(NewPCExpr);
        }
    }

    // release memory
    delete[] MergeFlagVec;
}

static raw_ostream &print(llvm::raw_ostream &Out, MemoryBlock &Mem, ExecutionState &ES) {
    switch (Mem.getKind()) {
        case MemoryBlock::MK_Stack:
            Out << "[Stack]\n---------------------------------------------------------\n";
            break;
        case MemoryBlock::MK_Heap:
            Out << "[Heap]\n---------------------------------------------------------\n";
            break;
        case MemoryBlock::MK_Message:
            Out << "[Message]\n---------------------------------------------------------\n";
            break;
        case MemoryBlock::MK_Global:
            Out << "[Global]\n---------------------------------------------------------\n";
            break;
    }

    std::vector<std::string> CharVec;
    unsigned Bytes = 0;
    for (unsigned I = 0; I < Mem.size(); ++I) {
        auto *AV = ES.getValue(Mem.at(I), false);
        CharVec.emplace_back();
        std::string &Content = CharVec.back();
        Content.append("[").append(std::to_string(I)).append("] ");
        if (AV) {
            Bytes += AV->bytewidth();
            Content.append(AV->str());
        } else {
            Content.append("<").append(std::to_string(Bytes)).append(">");
            Bytes = 0;
        }
    }

    unsigned I = 0;
    while (I < CharVec.size()) {
        unsigned PrintedLen = 0;
        do {
            std::string &Str2P = CharVec[I++];
            Out << " " << Str2P << " ";
            PrintedLen += Str2P.length();
            PrintedLen += 2;
        } while (PrintedLen < 156 && I < CharVec.size());
        Out << "\n---------------------------------------------------------\n";
    }

    return Out;
}

raw_ostream &operator<<(llvm::raw_ostream &O, ExecutionState &ES) {
#ifndef NDEBUG
    if (ES.ForkBlock && ES.ForkBlock->hasName()) {
        O << "[Source Block] " << ES.ForkBlock->getName() << " @ " << ES.ForkBlockBr << "\n";
    }
#endif
    O << "[Current PC]\n";
    unsigned ID = 0;
    for (auto &E: ES.PC)
        O << "[" << ID++ << "] " << Z3::to_string(E) << "\n";
    return O;
}

MemoryBlock *ExecutionState::stackAllocate(Function *F, Type *Ty, unsigned int Num) {
    auto *Mem = new StackMemoryBlock(F, Ty, Num);
    StackMem.push_back(Mem);
    auto Offset = 0;
    while (auto *AbsVal = Mem->at(Offset)) {
        // the value is not managed by shared_ptr but class Memory, do not delete automatically
        std::shared_ptr<AbstractValue> SharedAbsVal(AbsVal, [](AbstractValue *) {});
        AbsValRevisionMap[AbsVal] = SharedAbsVal;
        Offset += AbsVal->bytewidth();
    }
    return Mem;
}

MemoryBlock *ExecutionState::heapAllocate(Type *Ty, unsigned int Num) {
    auto *Mem = new HeapMemoryBlock(Ty, Num);
    HeapMem.push_back(Mem);
    auto Offset = 0;
    while (auto *AbsVal = Mem->at(Offset)) {
        // the value is not managed by shared_ptr but class Memory, do not delete automatically
        std::shared_ptr<AbstractValue> SharedAbsVal(AbsVal, [](AbstractValue *) {});
        AbsValRevisionMap[AbsVal] = SharedAbsVal;
        Offset += AbsVal->bytewidth();
    }
    return Mem;
}

MemoryBlock *ExecutionState::globalAllocate(Type *Ty, unsigned int Num) {
    GlobalMem.push_back(new GlobalMemoryBlock(Ty, Num));
    return GlobalMem.back();
}

MemoryBlock *ExecutionState::messageAllocate(Type *Ty, unsigned int Num) {
    MessageMem = new MessageBuffer(Ty, Num);
    return MessageMem;
}

AbstractValue *ExecutionState::bindValue(Value *V, Value *OldV) {
    auto VBIt = RegisterMem->find(OldV);
    if (VBIt == RegisterMem->end()) {
        boundValue(OldV);
    }
    VBIt = RegisterMem->find(OldV);
    assert(VBIt != RegisterMem->end());
    RegisterMem->emplace(V, VBIt->second);
    return VBIt->second.get();
}

AbstractValue *ExecutionState::boundValue(Value *V) {
    auto VBIt = RegisterMem->find(V);
    if (VBIt != RegisterMem->end()) {
        auto RetAV = VBIt->second;
        assert(RetAV->bytewidth() == DL::getNumBytes(V->getType()));
        return RetAV.get();
    }
    if (auto *GAlias = dyn_cast<GlobalAlias>(V)) {
        // for this special constant, we do not create any abs value for it
        // just track its alias
        return boundValue(GAlias->getAliasee());
    } else if (auto *Const = dyn_cast<Constant>(V)) {
        return createAbstractValue4Constant(Const);
    } else {
        // we should never reach here, except for printing debugging info
        return nullptr;
    }
}

AbstractValue *ExecutionState::createAbstractValue4Constant(Constant *V) {
    if (auto *CI = dyn_cast<ConstantInt>(V)) {
        auto *AbsVal = registerAllocate(V);
        if (V->getType()->isIntegerTy(1)) {
            // we do not want i1 1 -> i8 -1, thus using zext
            AbsVal->set(Z3::bv_val(CI->getZExtValue(), AbsVal->bytewidth() * 8));
        } else {
            AbsVal->set(Z3::bv_val(CI->getSExtValue(), AbsVal->bytewidth() * 8));
        }
        return AbsVal;
    } else if (auto *CF = dyn_cast<ConstantFP>(V)) {
        auto *AbsVal = registerAllocate(V);
        // we do not support fp
        return AbsVal;
    } else if (isa<ConstantExpr>(V)) {
        // due to the transform pass, LowerConstantExpr, we should not have constant expr in instructions
        // in other cases, we ignore constant expr
        return registerAllocate(V);
    } else if (auto *GV = dyn_cast<GlobalVariable>(V)) {
        if (GV->isConstant() && GV->hasInitializer()) {
            auto *GPtr = dyn_cast<AddressValue>(registerAllocate(V));
            assert(GPtr);
            auto *GAddr = globalAllocate(GV->getType()->getPointerElementType(), 1);
            GPtr->assign(GAddr);
            auto *Initializer = GV->getInitializer();
            std::vector<Constant *> FlattenedAbsValVec;
            DL::flatten(Initializer, FlattenedAbsValVec);

            if (auto *CDA = dyn_cast_or_null<ConstantDataArray>(Initializer))
                ((GlobalMemoryBlock *) GAddr)->setConstantDataArray();

            auto Offset = 0;
            for (auto AV: FlattenedAbsValVec) {
                auto *GAV = GAddr->at(Offset);
                assert(GAV);
                GAV->assign(boundValue(AV));
                Offset += GAV->bytewidth();
            }
        }
    } else if (isa<ConstantPointerNull>(V)) {
        auto *AbsVal = registerAllocate(V);
        AbsVal->zeroInitialize();
        return AbsVal;
    } else {
        // values we "do not care"
        if (!(isa<BlockAddress>(V)
              || isa<DSOLocalEquivalent>(V)
              || isa<ConstantVector>(V)
              || isa<UndefValue>(V)
              || isa<Function>(V)
              || isa<GlobalIFunc>(V)
              || isa<ConstantTokenNone>(V)
              // we do not deal with aggregated data, we assume that the contained data items are used separately
              || isa<ConstantAggregateZero>(V)
              || isa<ConstantDataArray>(V)
              || isa<ConstantStruct>(V)
              || isa<ConstantArray>(V))) {
            errs() << *V << "\n";
            llvm_unreachable("Error: unknown don't-care value!");
        }
    }
    return registerAllocate(V);
}

AbstractValue *ExecutionState::registerAllocate(Value *V) {
    auto It = RegisterMem->find(V);
    if (It != RegisterMem->end()) {
        // this should happen only in a loop
        return It->second.get();
    }

    if (V->getType()->isPointerTy()) {
        auto AV = std::make_shared<AddressValue>();
        RegisterMem->emplace(V, AV);
        return AV.get();
    } else {
        auto AV = std::make_shared<ScalarValue>(DL::getNumBytes(V->getType()));
        RegisterMem->emplace(V, AV);
        return AV.get();
    }
}

void ExecutionState::registerDeallocate(Value *V) {
    auto It = RegisterMem->find(V);
    if (It != RegisterMem->end()) {
        RegisterMem->erase(It);
    }
}

z3::expr ExecutionState::condition(BasicBlock *Block, unsigned int K) {
    auto *Terminator = Block->getTerminator();
    if (!isa<SwitchInst>(Terminator) && !isa<BranchInst>(Terminator))
        return Z3::free_bool(); // condition that is not interesting

    if (isa<BranchInst>(Terminator) && !((BranchInst *) Terminator)->isConditional()) {
        assert(K == 0);
        return Z3::bool_val(true);
    }

    auto *Val = Terminator->getOperand(0);
    auto *ValAV = boundValue(Val);
    if (ValAV->poison())
        return Z3::free_bool(); // condition that is not interesting

    if (auto *SW = dyn_cast<SwitchInst>(Terminator)) {
        int64_t CaseVar;
        if (Z3::is_numeral_i64(ValAV->value(), CaseVar)) {
            unsigned KK = 2;
            for (; KK < SW->getNumOperands(); KK += 2) {
                int SWInt = (int) cast<ConstantInt>(SW->getOperand(KK))->getSExtValue();
                if (SWInt == CaseVar) break;
            }
            if (KK < SW->getNumOperands()) {
                return Z3::bool_val(K == KK / 2);
            } else {
                return Z3::bool_val(K == 0);
            }
        } else {
            z3::expr CaseCond = Z3::bool_val(true);
            if (K == 0) {
                // the default case
                std::vector<z3::expr> DefaultConds;
                for (unsigned I = 2; I < SW->getNumOperands(); I += 2) {
                    int SWInt = (int) cast<ConstantInt>(SW->getOperand(I))->getSExtValue();
                    auto ThisCond = Z3::ne(ValAV->value(), Z3::bv_val(SWInt, ValAV->bytewidth() * 8));
                    DefaultConds.push_back(ThisCond);
                }
                CaseCond = Z3::make_and(DefaultConds);
            } else {
                int SWInt = (int) cast<ConstantInt>(SW->getOperand(K * 2))->getSExtValue();
                CaseCond = Z3::eq(ValAV->value(), Z3::bv_val(SWInt, ValAV->bytewidth() * 8));
            }
            return CaseCond;
        }
    } else if (auto *Br = dyn_cast<BranchInst>(Terminator)) {
        if (Br->isConditional()) {
            auto Cond = Z3::bv_to_bool(ValAV->value());
            return K == 0 ? Cond : Z3::negation(Cond);
        }
    }
    return Z3::bool_val(true);
}

z3::expr ExecutionState::pc() const {
    if (PC.empty())
        return Z3::bool_val(true);
    if (PC.size() == 1)
        return Z3::is_free(PC[0]) ? Z3::bool_val(true) : PC[0];

    z3::expr_vector FinalPCVec = Z3::vec();
    for (auto &E: PC)
        FinalPCVec.push_back(E);

    // for pc, let us use the z3's mk_and to avoid unnecessary simplification in Z3::make_and
    // this is critical for inferring phi
    return z3::mk_and(FinalPCVec);
}

z3::expr ExecutionState::pc(unsigned I) const {
    return PC.at(I);
}

z3::expr ExecutionState::pc(unsigned I, unsigned N) const {
    auto Vec = Z3::vec();
    for (unsigned K = I; K < PC.size() && K - I < N; ++K) {
        Vec.push_back(pc(K));
    }
    if (Vec.empty())
        return Z3::bool_val(true);
    // for pc, let us use the z3's mk_and to avoid unnecessary simplification in Z3::make_and
    // this is critical for inferring phi
    return z3::mk_and(Vec);
}

AbstractValue *ExecutionState::getValue(AbstractValue *Val, bool Store) {
    if (!Val) return nullptr;

    if (!Store) {
        auto It = AbsValRevisionMap.find(Val);
        if (It != AbsValRevisionMap.end()) {
            return It->second.get();
        }
        // the value has not been revised yet, a read only value, return it directly
        return Val;
    } else {
        auto It = AbsValRevisionMap.find(Val);
        if (It == AbsValRevisionMap.end()) {
            // this should only happen when recovering exiting states from an initial state
            // the initial state does not contain memory allocated in the loop
            std::shared_ptr<AbstractValue> SharedAbsVal(Val, [](AbstractValue *) {});
            It = AbsValRevisionMap.insert(std::begin(AbsValRevisionMap), std::make_pair(Val, SharedAbsVal));
        }
        assert(It != AbsValRevisionMap.end());
        auto CurrentVal = It->second;
        if (Val->getKind() == AbstractValue::AVK_Scalar) {
            auto NewVal = std::make_shared<ScalarValue>(CurrentVal->bytewidth());
            if (!CurrentVal->poison()) NewVal->assign(CurrentVal.get());
            It->second = NewVal;
            return NewVal.get();
        } else {
            auto NewVal = std::make_shared<AddressValue>();
            if (!CurrentVal->poison()) NewVal->assign(CurrentVal.get());
            It->second = NewVal;
            return NewVal.get();
        }
    }
}

void ExecutionState::gc(Function *F) {
    // message buffer
    if (MessageMem) MessageMem->gc();

    // registers
    for (auto &B: *F) {
        for (auto &I: B) {
            if (!I.getType()->isVoidTy()) registerDeallocate(&I);
        }
    }
    for (unsigned K = 0; K < F->arg_size(); ++K) {
        registerDeallocate(F->getArg(K));
    }

    // stack & AbsValRevisionMap
    std::set<StackMemoryBlock *> GC;
    StackMem.pop(&GC);
    for (auto *St: GC) {
        for (auto *Val: *St) {
            if (!Val) return;
            auto It = AbsValRevisionMap.find(Val);
            assert(It != AbsValRevisionMap.end());
            AbsValRevisionMap.erase(It);
        }
        delete St;
    }
}

void ExecutionState::markCall() {
    StackMem.push();
}

bool ExecutionState::conflict(const z3::expr &E) {
    if (E.is_false()) return true;
    return std::any_of(PC.cbegin(), PC.cend(), [&E](const z3::expr &V) { return Z3::simplify(E, V).is_false(); });
}

void ExecutionState::addPC(const z3::expr &E) {
//    if (Z3::to_string(E).find("-1 x 0") != std::string::npos) {
//        outs() << "";
//    }
//    if (Z3::to_string(E).find("ip_hdr") != std::string::npos) {
//        if (Z3::to_string(pc()).find("icmp_echo_hdr") != std::string::npos) {
//            outs() << "";
//        }
//    }

    if (E.is_true() || E.is_false() || Z3::is_free(E)) {
        return;
    }

    if (E.is_eq() && Z3::is_naming(E.arg(0))) {
        auto NamedBytes = Z3::find_all(E.arg(0).arg(0), false,
                                       [](const z3::expr &E) { return E.decl().decl_kind() == Z3_OP_SELECT; });
        bool AllNamed = true;
        for (auto NB: NamedBytes) {
            auto NBID = Z3::id(NB);
            if (!named(NBID)) {
                if (AllNamed) AllNamed = false;
                NamedByteSet.insert(NBID);
            }
        }
        if (!AllNamed) this->PC.push_back(E);
    } else {
        auto Res = E;
        for (auto OnePC: PC) {
            Res = Z3::simplify(OnePC, Res);
        }
        if (!Res.is_true()) this->PC.push_back(Res);
    }
}

void ExecutionState::replacePC(unsigned From, const z3::expr &New) {
    assert(From < PC.size());
    while (PC.size() > From) {
        PC.pop_back();
    }
    PC.push_back(New);
}

bool ExecutionState::optimize(std::vector<std::pair<AddressValue *, z3::expr>> &Vec) {
    // Vec = { X.x1.0, xc==0; X.x1.xc, xc!=0 } => { X.x1.xc }
    if (Vec.size() != 2) return false;

    auto *AddrVal1 = Vec[0].first;
    auto *AddrVal2 = Vec[1].first;
    if (AddrVal1->size() != 1 || AddrVal2->size() != 1) return false;

    auto Mem1 = AddrVal1->base(0);
    auto Mem2 = AddrVal2->base(0);

    if (Mem1 != Mem2) return false;

    auto Cond1 = Vec[0].second.simplify();
    auto Cond2 = Vec[1].second.simplify();

    if (!(Cond1 && Cond2).simplify().is_false()) return false;

    auto Off1 = AddrVal1->offset(0).simplify();
    auto Off2 = AddrVal2->offset(0).simplify();

    if (Cond2.is_eq()) {
        auto Cond = Cond2;
        Cond2 = Cond1;
        Cond1 = Cond;

        auto Off = Off2;
        Off2 = Off1;
        Off1 = Off;

        auto *AddrVal = AddrVal2;
        AddrVal2 = AddrVal1;
        AddrVal1 = AddrVal;
    }

    if (Cond1.is_eq()) {
        auto From = Z3::vec();
        auto To = Z3::vec();
        From.push_back(Cond1.arg(0));
        To.push_back(Cond1.arg(1));
        if (Z3::same(Off2.substitute(From, To).simplify(), Off1)) {
            Vec.clear();
            Vec.emplace_back(AddrVal2, Z3::bool_val(true));
            return true;
        } else if (Z3::same(Off2.substitute(To, From).simplify(), Off1)) {
            Vec.clear();
            Vec.emplace_back(AddrVal2, Z3::bool_val(true));
            return true;
        }
    }
    return false;
}

std::shared_ptr<AddressValue>
ExecutionState::optimize2(std::vector<std::pair<AddressValue *, z3::expr>> &Vec, unsigned PhiID) {
    // Vec = { X.x1, c1; X.x2, c2 } => { X.x1.phi(x1,c1,x2,c2) }
    auto ValVec = Z3::vec();
    auto CondVec = Z3::vec();
    for (unsigned K = 0; K < Vec.size(); ++K) {
        auto *AddrVal = Vec[K].first;
        if (AddrVal->size() != 1) return nullptr;
        auto Mem = AddrVal->base(0);
        if (!isa_and_nonnull<MessageBuffer>(Mem)) return nullptr;

        auto Off = AddrVal->offset(0).simplify();
        auto Cond = Vec[K].second;
        ValVec.push_back(Off);
        CondVec.push_back(Cond);
    }
    return std::make_shared<AddressValue>(Vec[0].first->base(0), Z3::make_phi(PhiID, ValVec, CondVec));
}
