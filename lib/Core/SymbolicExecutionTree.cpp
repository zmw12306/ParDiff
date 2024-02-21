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
#include "Core/SymbolicExecutionTree.h"
#include "Support/ADT.h"
#include "Support/Debug.h"

using namespace llvm;

void SymbolicExecutionTreeNode::addChild(SymbolicExecutionTreeNode *E) {
    Children.insert(E);
    E->Parent = this;
}

SymbolicExecutionTree::~SymbolicExecutionTree() {
    std::vector<SymbolicExecutionTreeNode *> GCStack;
    std::set<SymbolicExecutionTreeNode *> Visited;
    GCStack.push_back(Root);
    while (!GCStack.empty()) {
        auto *Top = GCStack.back();
        GCStack.pop_back();
        if (Visited.count(Top)) continue;
        Visited.insert(Top);
        for (auto *Ch: Top->Children) {
            GCStack.push_back(Ch);
        }
        delete Top;
    }
}

void SymbolicExecutionTree::dot(std::string &File, const char *NameSuffix) const {
    StringRef FileName(File);
    if (FileName.endswith(".dot")) {
        FileName = FileName.substr(0, FileName.size() - 4);
    }
    auto RealFileNameStr = FileName.str();
    RealFileNameStr = RealFileNameStr + "." + NameSuffix + ".dot";
    std::error_code EC;
    raw_fd_ostream DotStream(RealFileNameStr, EC, sys::fs::F_None);
    if (DotStream.has_error()) {
        errs() << "[Error] Cannot open the file <" << RealFileNameStr << "> for writing.\n";
        return;
    }

    auto DotNode = [](SymbolicExecutionTreeNode *Node, raw_ostream &OS) {
        const char *EntryExitStyle = R"(shape=record,color="#3d50c3ff", style=filled, fillcolor="#abc8fd70")";
        const char *OtherStyle = R"(shape=record,color="#b70d28ff", style=filled, fillcolor="#b70d2870")";
        bool RootOrLeaves = Node->Parent == nullptr || Node->Children.empty();
        OS << "\ta" << Node << "[" << (RootOrLeaves ? EntryExitStyle : OtherStyle) << ", label=\"{";
        auto Str = Z3::to_string(Node->Expr, true);
        if (Str.length() > 100)
            Str = Str.substr(0, 100) + "...";
        OS << ADT::autoNewLine(Str, 30, "\\l") << "\\l";
        OS << "}\"];\n";
        for (auto *Ch: Node->Children) OS << "\ta" << Node << "->a" << Ch << ";\n\n";
    };

    DotStream << "digraph slice {\n";
    std::vector<SymbolicExecutionTreeNode *> DotStack;
    std::set<SymbolicExecutionTreeNode *> Visited;
    DotStack.push_back(Root);
    unsigned X = 0;
    while (!DotStack.empty()) {
        auto *Top = DotStack.back();
        DotStack.pop_back();
        if (Visited.count(Top)) continue;
        Visited.insert(Top);
        DotNode(Top, DotStream);
        if (++X > 1000) break;
        for (auto *Ch: Top->Children) {
            DotStack.push_back(Ch);
        }
    }
    DotStream << "}\n";
    pardiff_INFO(RealFileNameStr << " dotted!");
}

void SymbolicExecutionTree::simplify() {
    // step 0: remove infeasible paths
    compressInfeasiblePaths();

    // step 1: remove redundant parent-children relations
    compressOffsprings();

    // step 2: remove redundant sibling relations
    compressSiblings();
}

void SymbolicExecutionTree::compressInfeasiblePaths() {
    std::vector<SymbolicExecutionTreeNode *> FalseNodeVec;
    std::stack<SymbolicExecutionTreeNode *> DFSStack;
    DFSStack.push(Root);
    while (!DFSStack.empty()) {
        auto Top = DFSStack.top();
        DFSStack.pop();

        if (Top->getExpr().is_false()) {
            assert(Top != Root);
            assert(Top->Children.empty());
            FalseNodeVec.push_back(Top);
        }

        for (auto *Ch: Top->Children) {
            //if (!Ch->Children.empty())
                DFSStack.push(Ch);
        }
    }

    while (!FalseNodeVec.empty()) {
        auto FalseNode = FalseNodeVec.back();
        FalseNodeVec.pop_back();
        assert(FalseNode != Root);

        // remove FalseNode
        auto *Parent = FalseNode->Parent;
        Parent->Children.erase(FalseNode);
        FalseNode->Parent = nullptr;
        delete FalseNode;

        if (Parent->Children.empty()) {
            FalseNodeVec.push_back(Parent);
        }
    }
}

void SymbolicExecutionTree::compressOffsprings() {
    auto NotRelated = [](const z3::expr &E) {
        return E.is_false() || E.is_true() || Z3::is_free(E);
    };

    std::stack<SymbolicExecutionTreeNode *> DFSStack;
    DFSStack.push(Root);
    while (!DFSStack.empty()) {
        auto Top = DFSStack.top();
        DFSStack.pop();
        for (auto *Ch: Top->Children) {
            if (!Ch->Children.empty())
                DFSStack.push(Ch);
        }

        if (Top == Root) continue;

        auto *TopParent = Top->Parent;
        if (NotRelated(Top->getExpr()) || Z3::same(Top->getExpr(), TopParent->getExpr())) {
            TopParent->Children.erase(Top);
            for (auto *Ch: Top->Children) {
                TopParent->Children.insert(Ch);
                Ch->Parent = TopParent;
            }
            delete Top;
        }
    }
}

void SymbolicExecutionTree::compressSiblings() {
    std::stack<SymbolicExecutionTreeNode *> DFSStack;
    DFSStack.push(Root);
    while (!DFSStack.empty()) {
        auto Top = DFSStack.top();
        DFSStack.pop();

        auto IIt = Top->Children.begin();
        while (IIt != Top->Children.end()) {
            auto *I = *IIt;

            auto JIt = IIt;
            ++JIt;
            while (JIt != Top->Children.end()) {
                auto *J = *JIt;
                if (Z3::same(I->getExpr(), J->getExpr())) {
                    for (auto *JCh: J->Children) {
                        I->Children.insert(JCh);
                        JCh->Parent = I;
                    }
                    delete J;
                    JIt = Top->Children.erase(JIt);
                } else {
                    JIt++;
                }
            }
            IIt++;
        }

        for (auto *Ch: Top->Children) {
            DFSStack.push(Ch);
        }
    }
}

z3::expr SymbolicExecutionTree::pc() const {
    return pc(Root);
}

z3::expr SymbolicExecutionTree::pc(SymbolicExecutionTreeNode *Node) const {
    z3::expr_vector Vec = Z3::vec();
    for (auto *Ch: Node->Children) {
        Vec.push_back(pc(Ch));
    }
    if (Vec.empty())
        return Node->getExpr();
    return Node->getExpr() && z3::mk_or(Vec);
}
