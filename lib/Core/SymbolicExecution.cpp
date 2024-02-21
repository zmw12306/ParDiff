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
#include "Core/SymbolicExecution.h"
#include "Support/TimeRecorder.h"

#define DEBUG_TYPE "SymbolicExecution"

using namespace llvm;

static cl::opt<bool> SEDefense("pardiff-enable-safe-se", cl::desc("enable safe se"), cl::init(false));

static void select(std::map<unsigned, std::vector<unsigned>>::iterator It,
                   std::map<unsigned, std::vector<unsigned>>::iterator End,
                   PushPopVector<PhiPointer> &Combo,
                   SliceGraphNode *Node,
                   std::vector<std::pair<SliceGraphNode *, std::vector<PhiPointer>>> &Ret) {
    Combo.push();

    if (It != End) {
        auto ItCopy = It;
        ItCopy++;
        for (auto Y: It->second) {
            Combo.push();
            Combo.push_back({It->first, Y});
            select(ItCopy, End, Combo, Node, Ret);
            Combo.pop();
        }
    } else {
        Ret.emplace_back(Node, Combo.get());
    }

    Combo.pop();
}

SymbolicExecutionTree *SymbolicExecution::run(const z3::expr &PC, SliceGraph &SG) {
    findDupPhiVal(PC);
    auto *FakeRoot = new SymbolicExecutionTreeNode();
    auto *Tree = new SymbolicExecutionTree(FakeRoot);

    std::vector<std::pair<SliceGraphNode *, std::vector<PhiPointer>>> EntryStateVec;
    for (auto EntryIt = SG.entry_begin(), E = SG.entry_end(); EntryIt != E; ++EntryIt) {
        auto *Entry = *EntryIt;
        std::map<unsigned, std::vector<unsigned>> PhiSelectionMap; // phi_id -> possible value index
        evaluatePhi(Entry, PhiSelectionMap);

        PushPopVector<PhiPointer> Combination;
        auto It = PhiSelectionMap.begin();
        select(It, PhiSelectionMap.end(), Combination, Entry, EntryStateVec);
    }

    for (auto &State: EntryStateVec) {
        doSymbolicExecutionDFS(FakeRoot, State.first, State.second);
    }

    PhiSelectorStack.reset();
    BNFExecutionPath.reset();
    NamedElementStack.reset();
    PathCondStack.reset();
    return Tree;
}

void SymbolicExecution::evaluatePhi(SliceGraphNode *Node, std::map<unsigned int, std::vector<unsigned int>> &Ret) {
    std::set<unsigned> Visited;
    std::vector<z3::expr> Stack;
    Stack.push_back(Node->getCondition());
    while (!Stack.empty()) {
        auto Top = Stack.back();
        Stack.pop_back();
        if (Visited.count(Z3::id(Top))) continue;
        Visited.insert(Z3::id(Top));

        if (Z3::is_phi(Top)) {
            auto TopPhiID = Z3::phi_id(Top);
            auto It = PhiSelectorStack.find({TopPhiID, 0});
            if (It != PhiSelectorStack.end()) {
                auto Selected = Top.arg(It->Selected);
                if (!Visited.count(Z3::id(Selected))) {
                    Stack.push_back(Selected);
                }
                LLVM_DEBUG(dbgs() << "[SE] \t phi." << TopPhiID << " has selected " << It->Selected << "\n");
                LLVM_DEBUG(dbgs() << "[SE] \t ----------------------- \n");
                continue; // we have pushed the selected value to the stack
            } else if (!Ret.count(TopPhiID)) {
                auto &SelectVec = Ret[TopPhiID];
                for (unsigned I = 0; I < Top.num_args(); ++I) {
                    auto OrigCondID = Z3::phi_cond_id(TopPhiID, I);
                    if (NamedElementStack.contains(OrigCondID) && !isDupPhiVal(TopPhiID, I)) {
                        SelectVec.push_back(I);

                        auto Selected = Top.arg(I);
                        if (!Visited.count(Z3::id(Selected))) Stack.push_back(Selected);
                    }
                }
                if (SelectVec.empty()) {
                    // in this case, this phi escapes from its lifetime via store/load, any index is fine.
                    SelectVec.push_back(0);
                    if (!SEDefense) {
                        std::string ErrMsg = "Error: no value we can select from phi." + std::to_string(TopPhiID) + "!";
                        throw std::runtime_error(ErrMsg);
                    }
                    pardiff_WARN("Escaped phi." << std::to_string(TopPhiID));
                }
                LLVM_DEBUG(for (auto Y: SelectVec) dbgs() << "[SE] \t phi." << TopPhiID << " can select " << Y << "\n");
                LLVM_DEBUG(dbgs() << "[SE] \t ----------------------- \n");
                continue; // we have pushed the selected value to the stack
            } else {
                assert(Ret.count(TopPhiID));
                for (auto SelectedID: Ret[TopPhiID]) {
                    auto Selected = Top.arg(SelectedID);
                    if (!Visited.count(Z3::id(Selected))) {
                        Stack.push_back(Selected);
                    }
                }
                continue; // we have pushed the selected value to the stack
            }
        }

        for (unsigned K = 0; K < Top.num_args(); ++K) {
            auto TopArgK = Top.arg(K);
            if (Visited.count(Z3::id(TopArgK))) continue;
            Stack.push_back(TopArgK);
        }
    }
}

void SymbolicExecution::doSymbolicExecutionDFS(SymbolicExecutionTreeNode *PrevTreeNode, SliceGraphNode *CurrGraphNode,
                                               std::vector<PhiPointer> &PhiSelectors) {
    PhiSelectorStack.push();
    BNFExecutionPath.push();
    NamedElementStack.push();
    PathCondStack.push();
    LLVM_DEBUG(dbgs() << "[SE] Visit: " << CurrGraphNode->getCondition() << "\n");

    auto *CurrTreeNode = new SymbolicExecutionTreeNode;
    PrevTreeNode->addChild(CurrTreeNode);
    BNFExecutionPath.push_back(CurrGraphNode);
    NamedElementStack.add(CurrGraphNode->getConditionID());
    for (auto &Selector: PhiSelectors) PhiSelectorStack.add(Selector);

    // simplify and eliminate phi according to phi selectors
    auto SimplifiedExpr = doSymbolicExecutionSimplify(CurrGraphNode->getCondition());
    PathCondStack.push_back(SimplifiedExpr);
    LLVM_DEBUG(dbgs() << "[SE] \tSimplified: " << SimplifiedExpr << "\n");

    // set the assertion of the tree node
    CurrTreeNode->setExpr(SimplifiedExpr);

    // check feasibility and continue
    if (!SimplifiedExpr.is_false()) {
        if (CurrGraphNode->getNumChildren() == 0) {
            auto *FakeExit = new SymbolicExecutionTreeNode;
            CurrTreeNode->addChild(FakeExit);
        } else {
            std::vector<std::pair<SliceGraphNode *, std::vector<PhiPointer>>> ChildStateVec;
            for (auto ChIt = CurrGraphNode->child_begin(), ChE = CurrGraphNode->child_end(); ChIt != ChE; ++ChIt) {
                auto *Ch = *ChIt;
                std::map<unsigned, std::vector<unsigned>> PhiSelectionMap; // phi_id -> possible value index
                evaluatePhi(Ch, PhiSelectionMap);

                PushPopVector<PhiPointer> Combination;
                auto It = PhiSelectionMap.begin();
                select(It, PhiSelectionMap.end(), Combination, Ch, ChildStateVec);
            }

            for (auto &ChState: ChildStateVec) {
                doSymbolicExecutionDFS(CurrTreeNode, ChState.first, ChState.second);
            }
        }
    } else {
        CurrTreeNode->setExpr(Z3::bool_val(false));
    }

    PathCondStack.pop();
    NamedElementStack.pop();
    PhiSelectorStack.pop();
    BNFExecutionPath.pop();
}

z3::expr SymbolicExecution::doSymbolicExecutionSimplify(const z3::expr &Assert) {
    // step 1: eliminate phi
    auto SimplifiedExpr = doSymbolicExecutionEliminatePhi(Assert);
    LLVM_DEBUG(dbgs() << "[SE] \tAfter eliminating phi: " << SimplifiedExpr << "\n");

    // step 2: remove redundant naming
    SimplifiedExpr = doSymbolicExecutionEliminateUselessNaming(SimplifiedExpr);
    LLVM_DEBUG(dbgs() << "[SE] \tAfter eliminating naming: " << SimplifiedExpr << "\n");

    // step 3: check if there is a conflict
    SimplifiedExpr = doSymbolicExecutionEliminateConflict(SimplifiedExpr);
    LLVM_DEBUG(dbgs() << "[SE] \tAfter eliminating conflict: " << SimplifiedExpr << "\n");

    return SimplifiedExpr;
}

z3::expr SymbolicExecution::doSymbolicExecutionEliminateConflict(const z3::expr &Expr) {
    if (Z3::is_naming_eq(Expr))
        return Expr;
    for (auto C: PathCondStack) {
        if (Z3::is_naming_eq(C)) continue;
        auto Ret = Z3::simplify(C, Expr);
        if (Ret.is_const())
            return Ret;
    }
    return Expr;
}

z3::expr SymbolicExecution::doSymbolicExecutionEliminatePhi(const z3::expr &Expr) {
    if (Expr.is_const()) {
        return Expr;
    } else if (Z3::is_phi(Expr)) {
        auto It = PhiSelectorStack.find({Z3::phi_id(Expr), 0});
        assert (It != PhiSelectorStack.end());
        LLVM_DEBUG(dbgs() << "[SE] \tphi." << It->PhiID << " selects " << It->Selected << "\n");
        return doSymbolicExecutionEliminatePhi(Expr.arg(It->Selected));
    }

    auto Decl = Expr.decl();
    auto ArgVec = Z3::vec();
    for (auto I = 0; I < Expr.num_args(); ++I) {
        auto Arg = Expr.arg(I);
        Arg = doSymbolicExecutionEliminatePhi(Arg);
        ArgVec.push_back(Arg);
    }
    // todo we just select the first but we need to select a branch like phi
    if (Decl.decl_kind() == Z3_OP_ITE && Z3::is_free(ArgVec[0])) {
        return ArgVec[1];
    }
    return Decl(ArgVec);
}

z3::expr SymbolicExecution::doSymbolicExecutionEliminateUselessNaming(const z3::expr &Expr) {
    if (Expr.is_eq() && Z3::is_naming(Expr.arg(0))) {
        std::vector<unsigned> Elements;
        z3::expr_vector Selects = Z3::find_all(Expr, false, [](const z3::expr &E) {
            return E.decl().decl_kind() == Z3_OP_SELECT;
        });
        for (auto Select: Selects) {
            Elements.push_back(Z3::id(Select.arg(1)));
        }

        bool AllIndexNamed = true;
        for (auto Elmt: Elements) {
            if (!NamedElementStack.contains(Elmt)) {
                AllIndexNamed = false;
                break;
            }
        }
        if (AllIndexNamed) {
            return Z3::bool_val(true);
        } else {
            for (auto Elmt: Elements)
                NamedElementStack.add(Elmt);
        }
    }
    return Expr;
}

void SymbolicExecution::findDupPhiVal(const z3::expr &Expr) {
    // given a phi id, x,
    // if for all phi.x(v1c1; v2c2; v3c3; v4c4; ...)
    // v1c1=v2c2, then we only need to preserve one of them.
    auto AllPhiVec = Z3::find_all(Expr, true, [](const z3::expr &E) { return Z3::is_phi(E); });
    std::map<unsigned, std::vector<z3::expr>> PhiMap;
    for (auto Phi: AllPhiVec) PhiMap[Z3::phi_id(Phi)].push_back(Phi);
    for (auto &It: PhiMap) {
        auto PhiID = It.first;
        auto PhiVec = It.second;

        std::map<std::pair<unsigned, unsigned>, std::vector<unsigned>> EquivClass;
        auto First = PhiVec[0];
        for (unsigned K = 0; K < First.num_args(); ++K) {
            unsigned VID = Z3::id(First.arg(K));
            unsigned CID = Z3::phi_cond_id(PhiID, K);
            EquivClass[{VID, CID}].push_back(K);
        }
        auto ECIt = EquivClass.begin();
        while (ECIt != EquivClass.end()) {
            if (ECIt->second.size() == 1) {
                ECIt = EquivClass.erase(ECIt);
            } else {
                ++ECIt;
            }
        }
        if (EquivClass.empty()) continue;
        for (unsigned K = 1; K < PhiVec.size(); ++K) {
            auto CurrPhi = PhiVec[K];
            ECIt = EquivClass.begin();
            while (ECIt != EquivClass.end()) {
                auto ECVec = ECIt->second;
                bool Pass = true;
                for (unsigned L = 1; L < ECVec.size(); ++L) {
                    if (!Z3::same(CurrPhi.arg(ECVec[0]), CurrPhi.arg(ECVec[L]))) {
                        Pass = false;
                        break;
                    }
                }
                if (!Pass) {
                    ECIt = EquivClass.erase(ECIt);
                } else {
                    ++ECIt;
                }
            }
        }
        if (EquivClass.empty()) continue;
        ECIt = EquivClass.begin();
        while (ECIt != EquivClass.end()) {
            for (unsigned X = 1; X < ECIt->second.size(); ++X) {
                PhiID2DupValIDMap[PhiID].push_back(ECIt->second[X]);
            }
            ++ECIt;
        }
    }
}

bool SymbolicExecution::isDupPhiVal(unsigned int PhiID, unsigned int ValID) {
    auto It = PhiID2DupValIDMap.find(PhiID);
    if (It == PhiID2DupValIDMap.end())
        return false;
    auto &DupVec = It->second;
    return std::find(DupVec.begin(), DupVec.end(), ValID) != DupVec.end();
}
