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

#include <llvm/IR/Instructions.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Support/Debug.h>

#include "Transform/RemoveIrreducibleFunction.h"
#include "Support/Debug.h"

#define DEBUG_TYPE "RemoveIrreducibleFunction"

using namespace llvm;

char RemoveIrreducibleFunction::ID = 0;
static RegisterPass<RemoveIrreducibleFunction> X(DEBUG_TYPE, "Removing reducible function.");

//===------------------------------------------------------------------------===//
// GraphTraits specializations for using generic graph algorithms.
namespace llvm {
    template<>
    struct GraphTraits<CFGNode *> {
        using NodeRef = CFGNode *;
        typedef CFGNode::iterator ChildIteratorType;

        static NodeRef getEntryNode(CFGNode *SCFGN) { return SCFGN; }

        static inline ChildIteratorType child_begin(NodeRef NT) { return NT->begin(); }

        static inline ChildIteratorType child_end(NodeRef NT) { return NT->end(); }
    };

    template<>
    struct GraphTraits<const CFGNode *> {
        using NodeRef = const CFGNode *;
        typedef CFGNode::iterator ChildIteratorType;

        static NodeRef getEntryNode(const CFGNode *SCFGN) { return SCFGN; }

        static inline ChildIteratorType child_begin(NodeRef NT) { return NT->begin(); }

        static inline ChildIteratorType child_end(NodeRef NT) { return NT->end(); }
    };

    template<>
    struct GraphTraits<CFG *> : public GraphTraits<CFGNode *> {
        static NodeRef getEntryNode(CFG *SCFG) { return SCFG->getEntry(); }

        typedef CFG::iterator nodes_iterator;

        static nodes_iterator nodes_begin(CFG *SCFG) { return SCFG->begin(); }

        static nodes_iterator nodes_end(CFG *SCFG) { return SCFG->end(); }
    };

    template<>
    struct GraphTraits<const CFG *> : public GraphTraits<const CFGNode *> {
        static NodeRef getEntryNode(const CFG *SCFG) { return SCFG->getEntry(); }

        typedef CFG::const_iterator nodes_iterator;

        static nodes_iterator nodes_begin(const CFG *SCFG) { return SCFG->begin(); }

        static nodes_iterator nodes_end(const CFG *SCFG) { return SCFG->end(); }
    };
} // end of the graph traits

RemoveIrreducibleFunction::RemoveIrreducibleFunction() : FunctionPass(ID) {}

RemoveIrreducibleFunction::~RemoveIrreducibleFunction() = default;

void RemoveIrreducibleFunction::getAnalysisUsage(AnalysisUsage &AU) const {}

bool RemoveIrreducibleFunction::runOnFunction(Function &F) {
    if (F.isDeclaration()) return false;
    CFG FuncCFG(F);
    LLVM_DEBUG(dbgs() << "T1 & T2 transforms..." << "\n");
    FuncCFG.t1t2();
    LLVM_DEBUG(dbgs() << "Done! Graph size after transforms: " << FuncCFG.size() << ".\n");
    LLVM_DEBUG(if (FuncCFG.size() > 1) dbgs() << FuncCFG << "\n");

    if (FuncCFG.size() == 1) {
        return false;
    } else {
        F.deleteBody();
        F.setComdat(nullptr);
        pardiff_WARN(F.getName() << " contains irreducible loops!");
        return true;
    }
}

CFG::CFG(Function &F) : Entry(nullptr) {
    for (auto &B: F) {
        auto *Node = new CFGNode;
        Node->addBlock(&B);
        BlockNodeMap[&B] = Node;
        Nodes.insert(Node);
    }
    Entry = BlockNodeMap[&F.getEntryBlock()];

    std::stack<CFGNode *> WorkStack;
    for (auto &Node: Nodes) {
        BasicBlock &BB = *((*Node)[0]);
        for (auto SuccIt = succ_begin(&BB), End = succ_end(&BB); SuccIt != End;
             SuccIt++) {
            Node->Succs.insert(BlockNodeMap[*SuccIt]);
        }

        for (auto PredIt = pred_begin(&BB), End = pred_end(&BB); PredIt != End;
             PredIt++) {
            Node->Preds.insert(BlockNodeMap[*PredIt]);
        }

        if (Node->Preds.empty() && (*Node)[0] != (*Entry)[0]) {
            WorkStack.push(Node);
        }
    }

    // delete dead blocks
    while (!WorkStack.empty()) {
        auto Node = WorkStack.top();
        WorkStack.pop();

        for (auto Succ: Node->Succs) {
            Succ->Preds.erase(Node);
            if (Succ->Preds.empty()) {
                WorkStack.push(Succ);
            }
        }

        Nodes.erase(Node);
    }
}

CFG::~CFG() {
    LLVM_DEBUG(dbgs() << "Releasing memory allocated for cfg..." << "\n");
    std::set<CFGNode *> ReleasedSet;
    for (auto &It: BlockNodeMap) {
        if (!ReleasedSet.count(It.second)) {
            ReleasedSet.insert(It.second);
            delete It.second;
        }
    }
    LLVM_DEBUG(dbgs() << "Done!" << "\n");
}

void CFG::t1t2() {
    unsigned OrigSize;
    unsigned CurrSize;
    do {
        OrigSize = Nodes.size();
        t1();
        t2();
        CurrSize = Nodes.size();
    } while (OrigSize != CurrSize);
}

void CFG::t1() {
    for (auto &Node: Nodes) {
        auto PredIt = Node->Preds.find(Node);
        if (PredIt != Node->Preds.end()) {
            Node->Preds.erase(PredIt);
        }

        auto SuccIt = Node->Succs.find(Node);
        if (SuccIt != Node->Succs.end()) {
            Node->Succs.erase(SuccIt);
        }
    }
}

void CFG::t2() {
    std::stack<CFGNode *> WorkStack;
    std::set<CFGNode *> WorkListCopy;
    for (auto &Node: Nodes) {
        WorkStack.push(Node);
        WorkListCopy.insert(Node);
    }

    while (!WorkStack.empty()) {
        auto Node = WorkStack.top();
        WorkStack.pop();
        WorkListCopy.erase(Node);

        LLVM_DEBUG(dbgs() << "Checking node: " << (*Node)[0]->getName() << "(" << Node << ")" << "\n");

        if (Node->Preds.size() == 1) {
            CFGNode *PredNode = *(Node->Preds.begin());
            assert(PredNode != Node);
            PredNode->Succs.erase(Node);
            // "Node" is contracted to "PredNode"
            for (size_t I = 0; I < Node->numBlocks(); I++) {
                BlockNodeMap[(*Node)[I]] = PredNode;
                PredNode->addBlock((*Node)[I]);
            }

            for (auto SuccNode: Node->Succs) {
                SuccNode->Preds.erase(Node);
                if (SuccNode != PredNode) {
                    SuccNode->Preds.insert(PredNode);
                    PredNode->Succs.insert(SuccNode);
                }
                if (SuccNode->Preds.size() == 1 &&
                    !WorkListCopy.count(SuccNode)) {
                    WorkStack.push(SuccNode);
                    WorkListCopy.insert(SuccNode);
                }
            }
            Nodes.erase(Node);
            LLVM_DEBUG(dbgs() << "Removing node " << (*Node)[0]->getName() << "(" << Node << ")" << "\n");
            delete Node;
        }
    }
}

raw_ostream &operator<<(raw_ostream &OS, const CFG &FuncCFG) {
    OS << "=================\n";
    for (auto &Node: FuncCFG) {
        OS << (*Node)[0]->getName() << "\n";
        OS << "\t Preds: ";
        for (auto It = Node->pred_begin(), E = Node->pred_end(); It != E; ++It) {
            auto *PredNode = *It;
            OS << (*PredNode)[0]->getName() << ", ";
        }
        OS << "\n";
        OS << "\t Succs: ";
        for (auto SussNode: *Node) {
            OS << (*SussNode)[0]->getName() << ", ";
        }
        OS << "\n";
    }

    // a simple validation procedure
    for (auto &Node: FuncCFG) {
        for (auto It = Node->pred_begin(), E = Node->pred_end(); It != E; ++It) {
            auto *PredNode = *It;
            assert(PredNode->countSucc(Node));
        }

        for (auto &SussNode: *Node) {
            assert(SussNode->countPred(Node));
        }
    }

    OS << "-----------------\n";
    OS << "digraph CFG {\n";
    for (auto &Node: FuncCFG) {
        OS << "\tNode" << Node << "[shape=record,label=\"";
        for (size_t I = 0; I < Node->numBlocks(); I++) {
            auto BB = (*Node)[I];
            OS << BB->getName() << "\\l";
            if (I > 10)
                break;
        }
        OS << "\"]\n";

        for (auto It = Node->pred_begin(), E = Node->pred_end(); It != E; ++It) {
            auto *PredNode = *It;
            OS << "\tNode" << PredNode << " -> Node" << Node << "\n";
        }
    }
    OS << "}\n";

    return OS << "=================";
}