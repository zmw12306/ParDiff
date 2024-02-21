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
#include <llvm/Support/MD5.h>
#include "Core/SliceGraph.h"
#include "Support/ADT.h"
#include "Support/Debug.h"
#include "BNF/BNF.h"
#include <queue>
#include <deque>

#define DEBUG_TYPE "SliceGraph"

using namespace llvm;

static cl::opt<std::string> SimplifyMode("pardiff-slice-mode",
                                         cl::desc("mode: full, name, formula"),
                                         cl::init("full"));

static std::map<unsigned, std::set<unsigned>> ForkMap;
static std::set<unsigned> PhiCondID;
static bool OldVersion = false;

static bool uselessPhi(const z3::expr &E) {
    assert(Z3::is_phi(E));
    for (unsigned K = 0; K < E.num_args(); ++K) {
        auto Arg = E.arg(K);
        if (!Arg.is_true() && !Z3::is_free(Arg)) {
            return false;
        }
    }
    return true;
}

SliceGraph *SliceGraph::getAnd(const z3::expr &And) {
    auto First = And.arg(0);
    auto *FirstGraph = getUnknown(First);
    for (unsigned I = 1; I < And.num_args(); ++I) {
        auto *G = getUnknown(And.arg(I));
        for (auto *Ex: FirstGraph->Exits) {
            for (auto *En: G->Entries) {
                Ex->Children.insert(En);
                En->Parents.insert(Ex);
            }
        }
        FirstGraph->Exits = G->Exits;
        G->Entries.clear(); // clear the entries so that the following delete will not del the vertices
        delete G;
    }
    return FirstGraph;
}

SliceGraph *SliceGraph::getOr(const z3::expr &Or) {
    if (OldVersion) {
        assert(Or.num_args() > 0);
        SliceGraph *FirstGraph = getUnknown(Or.arg(0));
        for (unsigned I = 1; I < Or.num_args(); ++I) {
            auto *G = getUnknown(Or.arg(I));
            FirstGraph->Entries.insert(G->Entries.begin(), G->Entries.end());
            FirstGraph->Exits.insert(G->Exits.begin(), G->Exits.end());
            G->Entries.clear(); // clear the entries so that the following delete will not del the vertices
            delete G;
        }
        return FirstGraph;
    }

    std::set<unsigned> *ForkSet;
    auto It = ForkMap.find(Z3::id(Or));
    if (It != ForkMap.end()) {
        ForkSet = &It->second;
    } else {
        return getGraph(Or);
    }

    z3::expr_vector RemainingExprVec = Z3::vec();
    SliceGraph *OrG = new SliceGraph;
    for (unsigned I = 0; I < Or.num_args(); ++I) {
        if (!ForkSet->count(Z3::id(Or.arg(I)))) {
            RemainingExprVec.push_back(Or.arg(I));
            continue;
        }
        auto *G = getUnknown(Or.arg(I));
        auto *GRoot = new SliceGraphNode(Z3::bool_val(true));
        if (PhiCondID.count(Z3::id(Or.arg(I)))) {
            GRoot->setConditionID(Z3::id(Or.arg(I)));
        }
        for (auto *X: G->Entries) {
            X->Parents.insert(GRoot);
            GRoot->Children.insert(X);
        }
        OrG->Entries.insert(GRoot);
        OrG->Exits.insert(G->Exits.begin(), G->Exits.end());
        G->Entries.clear(); // clear the entries so that the following delete will not del the vertices
        delete G;
    }

    if (!RemainingExprVec.empty()) {
        auto RemainingExpr = RemainingExprVec.size() == 1 ? RemainingExprVec[0] : z3::mk_or(RemainingExprVec);
        SliceGraph *G = getGraph(RemainingExpr);
        OrG->Entries.insert(G->Entries.begin(), G->Entries.end());
        OrG->Exits.insert(G->Exits.begin(), G->Exits.end());
        G->Entries.clear(); // clear the entries so that the following delete will not del the vertices
        delete G;
    }
    return OrG;
}

SliceGraph *SliceGraph::getUnknown(const z3::expr &Unk) {
    if (Unk.is_and()) {
        return getAnd(Unk);
    } else if (Unk.is_or()) {
        return getOr(Unk);
    } else {
        return getGraph(Unk);
    }
}

SliceGraph *SliceGraph::getGraph(const z3::expr &Unk) {
    // remove useless phi
    auto E = Unk;
    auto PhiVec = Z3::find_all(Unk, true, [](const z3::expr &E) {
        return Z3::is_phi(E) && uselessPhi(E);
    });
    if (!PhiVec.empty()) {
        auto To = Z3::vec();
        for (unsigned K = 0; K < PhiVec.size(); ++K) To.push_back(Z3::bool_val(true));
        E = E.substitute(PhiVec, To);
    }

    // create a graph with one in and one out
    auto *Graph = new SliceGraph;
    auto *Node = new SliceGraphNode(E);
    Graph->Entries.insert(Node);
    Graph->Exits.insert(Node);
    return Graph;
}



SliceGraph *SliceGraph::get(const z3::expr PC, bool AllExpanded) {
    if (AllExpanded) {
        OldVersion = true;
        auto *BigGraph = getUnknown(PC);
        OldVersion = false;
        pardiff_INFO("Slice Size: " << BigGraph->size());
        return BigGraph;
    }

    auto PhiVec = Z3::find_all(PC, true, [](const z3::expr &E) { return Z3::is_phi(E); });
    auto OrVec = Z3::find_all(PC, true, [](const z3::expr &E) { return E.is_or(); });

    std::set<unsigned> OrArgID;
    for (auto Or: OrVec) {
        for (unsigned K = 0; K < Or.num_args(); ++K) {
            auto Cond = Or.arg(K);
            assert(!Cond.is_false());
            OrArgID.insert(Z3::id(Cond));
        }
    }

    for (auto Phi: PhiVec) {
        if (uselessPhi(Phi)) continue;
        auto PhiID = Z3::phi_id(Phi);
        for (unsigned K = 0; K < Phi.num_args(); ++K) {
            auto CondID = Z3::phi_cond_id(PhiID, K);
            if (!OrArgID.count(CondID)) {
                errs() << "cond id : " << CondID << "\n";
                errs() << "phi id : " << Z3::phi_id(Phi) << "\n";
                assert(false);
            }
            PhiCondID.insert(CondID);
        }
    }

    std::map<unsigned, std::vector<z3::expr>> ReferenceMap;
    std::set<unsigned> Visited;
    std::vector<z3::expr> Stack;
    Stack.push_back(PC);
    while (!Stack.empty()) {
        auto Top = Stack.back();
        Stack.pop_back();
        auto TopID = Z3::id(Top);
        if (Visited.count(TopID)) continue;
        Visited.insert(TopID);

        if (Top.is_or() || Top.is_and()) {
            for (unsigned K = 0; K < Top.num_args(); ++K) {
                auto TopK = Top.arg(K);
                auto TopKID = Z3::id(TopK);
                ReferenceMap[TopKID].push_back(Top);
                Stack.push_back(TopK);
            }
        }
    }

    std::vector<unsigned> PhiCondIDWorkList;
    PhiCondIDWorkList.insert(PhiCondIDWorkList.end(), PhiCondID.begin(), PhiCondID.end());
    while (!PhiCondIDWorkList.empty()) {
        auto CID = PhiCondIDWorkList.back();
        PhiCondIDWorkList.pop_back();

        auto It = ReferenceMap.find(CID);
        if (It == ReferenceMap.end()) {
            assert(CID == Z3::id(PC));
            continue;
        }
        auto &References = It->second;
        for (auto &Ref: References) {
            auto RefID = Z3::id(Ref);
            if (!ForkMap.count(RefID)) {
                PhiCondIDWorkList.push_back(RefID);
            }
            if (Ref.is_and()) {
                ForkMap[RefID];
            } else if (Ref.is_or()) {
                ForkMap[RefID].insert(CID);
            } else {
                assert(false);
            }
        }
    }

    auto *Graph = SliceGraph::getUnknown(PC);
    pardiff_INFO("Slice Size: " << Graph->size());

    // each phi condition should be a node in the graph
    std::vector<SliceGraphNode *> NodeStack;
    std::set<SliceGraphNode *> NodeVisited;
    std::set<unsigned> CondIDSet;
    for (auto *En: Graph->Entries)
        NodeStack.push_back(En);
    while (!NodeStack.empty()) {
        auto *Top = NodeStack.back();
        NodeStack.pop_back();
        if (NodeVisited.count(Top)) continue;
        NodeVisited.insert(Top);
        CondIDSet.insert(Top->getConditionID());
        for (auto *Ch: Top->Children) {
            NodeStack.push_back(Ch);
        }
    }
    for (auto CID: PhiCondID) {
        assert(CondIDSet.count(CID));
    }

    // release memory
    std::map<unsigned, std::set<unsigned>>().swap(ForkMap);
    std::set<unsigned>().swap(PhiCondID);
    return Graph;
}

SliceGraph::~SliceGraph() {
    std::vector<SliceGraphNode *> GCStack;
    std::set<SliceGraphNode *> Visited;
    for (auto *En: Entries)
        GCStack.push_back(En);
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

unsigned SliceGraph::size() const {
    unsigned Size = 0;
    dfs([&Size](SliceGraphNode *N) { Size++; });
    return Size;
}

void SliceGraph::dot(std::string &File, const char *NameSuffix) const {
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
    

    auto DotNode = [](SliceGraphNode *Node, raw_ostream &OS) {
        const char *NodeStyle = R"(shape=record, color="#3d50c3ff", style=filled, fillcolor=)";
        bool RootOrLeaves = Node->Parents.empty() || Node->Children.empty();
        if (auto *Color = Node->getColor()) {
            OS << "\ta" << Node << "[" << NodeStyle << "\"" << Color << "\"" << ", label=\"{";
            //errs()<<"aaa\n";
        } else {
            OS << "\ta" << Node << "[" << NodeStyle << (RootOrLeaves ? R"("#abc8fd70")" : R"("#b70d2870")")
               << ", label=\"{";
            //errs()<<"bbb\n";
        }
        if (!Node->getHint().empty()) {
            OS << Node->getHint();
            //errs()<<"ccc\n";
        } else if (Node->getConditionID() != Z3::id(Node->getCondition())) {
            assert(Node->getCondition().is_true());
            OS << "$" << Node->getConditionID();
            //errs()<<"ddd\n";
        } else {
            auto Str = Z3::to_string(Node->Condition, true);
            //errs()<<"fff\n";
            if (Str.length() > 100)
                Str = Str.substr(0, 100) + "...";
            OS << /*"[" << Node->X.substr(0, 4) << "] " <<*/ ADT::autoNewLine(Str, 30, "\\l") << "\\l";
        }
        OS << "}\"];\n";
        for (auto *Ch: Node->Children) OS << "\ta" << Node << "->a" << Ch << ";\n\n";
    };
    

    unsigned X = 0;
    DotStream << "digraph slice {\n";
    std::vector<SliceGraphNode *> DotStack;
    std::set<SliceGraphNode *> Visited;
    // errs()<<"entries size: "<<Entries.size()<<"\n";
    for (auto *En: Entries)
        DotStack.push_back(En);
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


void SliceGraph::remove(SliceGraphNode *N, bool PreserveReachability) {
    std::set<SliceGraphNode *> Deleted;
    remove(N, PreserveReachability, &Deleted);
}

void SliceGraph::remove(SliceGraphNode *N, bool PreserveReachability, std::set<SliceGraphNode *> *Deleted) {
    if (Deleted->count(N)) return;

    for (auto *NParent: N->Parents) {
        NParent->Children.erase(N);
    }
    for (auto *NChild: N->Children) {
        NChild->Parents.erase(N);
    }

    if (PreserveReachability)
        for (auto *NParent: N->Parents) {
            for (auto *NChild: N->Children) {
                NParent->Children.insert(NChild);
                NChild->Parents.insert(NParent);
            }
        }

    Entries.erase(N);
    Exits.erase(N);
    for (auto *NParent: N->Parents) {
        if (NParent->Children.empty())
            Exits.insert(NParent);
    }
    for (auto *NChild: N->Children) {
        if (NChild->Parents.empty()) {
            if (!PreserveReachability) {
                remove(NChild, PreserveReachability, Deleted);
            } else {
                Entries.insert(NChild);
            }
        }
    }

    if (Deleted)
        Deleted->insert(N);
    delete N;
}

void SliceGraph::simplifyAfterSymbolicExecution() {
    // simplifying formulas in each node
    simplifyByRewriting();

    // removing useless nodes
    simplifyByRemoving();

    // merging equivalent nodes
    simplifyByMerging();

    // share the same graph structure
    simplifyByHashConsing();

    pardiff_INFO("Slice Size: " << size());
}

void SliceGraph::simplifyByRewriting() {
    dfs([this](SliceGraphNode *N) {
        auto Expr = simplify(N->getCondition()).simplify();
        N->setCondition(Expr);
        N->setConditionID(Z3::id(Expr));
    });
}

void SliceGraph::simplifyByRemoving() {
    auto NotRelated = [](SliceGraphNode *Node) {
        auto Expr = Node->getCondition();
        z3::expr_vector Selects = Z3::find_all(Expr, false, [](const z3::expr &E) {
            return E.decl().decl_kind() == Z3_OP_SELECT;
        });
        if (SimplifyMode.getValue() == "name") {
            return !(Expr.is_eq() && Z3::is_naming(Expr.arg(0)));
        } else if (SimplifyMode.getValue() == "formula") {
            return (Expr.is_eq() && Z3::is_naming(Expr.arg(0))) || Selects.empty();
        }
        return Selects.empty();
    };

    std::set<SliceGraphNode *> Visited;
    dfs([&Visited](SliceGraphNode *N) {
        Visited.insert(N);
    });

    // remove false nodes.
    std::set<SliceGraphNode *> Deleted;
    auto It = Visited.begin();
    while (It != Visited.end()) {
        auto *N = *It;
        if (Deleted.count(N)) {
            It = Visited.erase(It);
            continue;
        }
        if (!N->getCondition().is_false()) {
            It++;
            continue;
        }

        remove(N, false, &Deleted);
        It = Visited.erase(It);
    }
    for (auto *Del: Deleted)
        Visited.erase(Del);
    Deleted.clear();

    // remove not related nodes.
    It = Visited.begin();
    while (It != Visited.end()) {
        auto *N = *It;
        if (!NotRelated(N)) {
            It++;
            continue;
        }

        remove(N, true);
        It = Visited.erase(It);
    }

    // do some check
    for (auto *Node: Visited) validate(Node);
}

void SliceGraph::simplifyByMerging() {
    std::set<SliceGraphNode *> Deleted;
    std::set<SliceGraphNode *> Visited;
    dfs([&Visited](SliceGraphNode *N) {
        Visited.insert(N);
    });

    // remove equivalent nodes, preserving one only
    std::set<SliceGraphNode *> ToRemove;
    for (auto *N: Visited) {
        auto ChIt = N->Children.begin();
        while (ChIt != N->Children.end()) {
            auto *Ch = *ChIt;
            ChIt++;
            auto NextChIt = ChIt;
            while (NextChIt != N->Children.end()) {
                auto *NextCh = *NextChIt;
                NextChIt++;

                if (Ch->getConditionID() ==
                    NextCh->getConditionID() /*Z3::same(Ch->getCondition(), NextCh->getCondition())*/
                    && Ch->Parents == NextCh->Parents
                    && Ch->Children == NextCh->Children) {
                    ToRemove.insert(Ch);
                    break;
                }
            }
        }
    }
    for (auto *TR: ToRemove) {
        remove(TR, false, &Deleted);
        assert(Deleted.size() == 1);
        Deleted.clear();
        Visited.erase(TR);
    }

    // do some check
    for (auto *Node: Visited) validate(Node);

    // for merge
    ToRemove.clear();
    std::vector<SliceGraphNode *> Stack;
    for (auto *V: Visited) Stack.push_back(V);
    while (!Stack.empty()) {
        auto N = Stack.back();
        Stack.pop_back();

        auto ChIt = N->Children.begin();
        while (ChIt != N->Children.end()) {
            auto *Ch = *ChIt;
            bool ChMerged = false;

            auto NextChIt = ChIt;
            NextChIt++;
            while (NextChIt != N->Children.end()) {
                auto *NextCh = *NextChIt;
                NextChIt++;

                if (Ch->getConditionID() ==
                    NextCh->getConditionID() /*Z3::same(Ch->getCondition(), NextCh->getCondition())*/
                    && (Ch->Parents == NextCh->Parents || Ch->Children == NextCh->Children)) {
                    // merge Ch -> NextCh
                    for (auto P: Ch->Parents) {
                        NextCh->Parents.insert(P);
                        P->Children.insert(NextCh);
                    }
                    for (auto C: Ch->Children) {
                        NextCh->Children.insert(C);
                        C->Parents.insert(NextCh);
                    }
                    if (Entries.count(NextCh) && NextCh->getNumParents()) {
                        Entries.erase(NextCh);
                    }
                    if (Exits.count(NextCh) && NextCh->getNumChildren()) {
                        Exits.erase(NextCh);
                    }
                    ChMerged = true;
                    Stack.push_back(NextCh);
                    break;
                }
            }

            if (ChMerged) {
                ToRemove.insert(Ch);
                ChIt = N->Children.erase(ChIt);
                // make Ch a single node
                for (auto P: Ch->Parents)
                    P->Children.erase(Ch);
                for (auto C: Ch->Children)
                    C->Parents.erase(Ch);
                Ch->Parents.clear();
                Ch->Children.clear();
            } else {
                ChIt++;
            }
        }
    }
    for (auto *TR: ToRemove) {
        remove(TR, false, &Deleted);
        assert(Deleted.size() == 1);
        Deleted.clear();
        Visited.erase(TR);
    }

    // do some check
    for (auto *Node: Visited) validate(Node);
}

void SliceGraph::simplifyByHashConsing() {
    std::vector<SliceGraphNode *> Topo;
    topoOrder(Topo);

    // bottom-up to compute hash and merge those having the same hash
    std::map<SliceGraphNode *, std::string> NodeHashMap;
    std::map<std::string, SliceGraphNode *> HashNodeMap;
    std::set<std::string> Children;
    for (unsigned I = Topo.size(); I > 0; --I) {
        auto *N = Topo[I - 1];

        std::string Str = std::to_string(N->getConditionID());
        Children.clear();
        for (auto *Ch: N->Children) {
            Children.insert(NodeHashMap[Ch]);
        }
        for (auto &Ch: Children) {
            Str.append(".").append(Ch);
        }

        MD5 Hash;
        Hash.update(Str);
        MD5::MD5Result Res;
        Hash.final(Res);
        auto Digest = Res.digest().str().str();
        NodeHashMap[N] = Digest;
        auto It = HashNodeMap.find(Digest);
        if (It == HashNodeMap.end()) {
            HashNodeMap[Digest] = N;
        } else {
            // merge, N's all parents should connect to SameHashNode
            auto *SameHashNode = It->second;
            for (auto *NParent: N->Parents) {
                NParent->Children.insert(SameHashNode);
                SameHashNode->Parents.insert(NParent);
                NParent->Children.erase(N);
            }
            N->Parents.clear();
            remove(N, false);
        }
    }

    // do some check
    dfs([this](SliceGraphNode *N) { validate(N); });
}

static bool isFree(const z3::expr &E) {
    if (E.is_const()) {
        return Z3::is_free(E);
    } else {
        for (unsigned K = 0; K < E.num_args(); ++K) {
            if (!isFree(E.arg(K))) {
                return false;
            }
        }
        return true;
    }
}

void SliceGraph::simplifyBeforeSymbolicExecution() {
    // step 1
    std::set<SliceGraphNode *> Visited;
    dfs([&Visited](SliceGraphNode *N) {
        Visited.insert(N);
    });
    std::set<SliceGraphNode *> ToRemove;
    for (auto N: Visited) {
        if (isFree(N->getCondition())) {
            ToRemove.insert(N);
        }
        if (N->getCondition().is_true() && N->getConditionID() == Z3::id(N->getCondition())) {
            ToRemove.insert(N);
        }
    }
    for (auto *X: ToRemove) remove(X, true);

    // step 2
    simplifyByMerging();

    // step 3
    simplifyByHashConsing();

    pardiff_INFO("Slice Size: " << size());
}

void SliceGraph::validate(SliceGraphNode *N) const {
    assert(!N->Children.count(N));
    assert(!N->Parents.count(N));
    assert(!Entries.count(N) || N->getNumParents() == 0);
    assert(N->getNumParents() != 0 || Entries.count(N));
    assert(!Exits.count(N) || N->getNumChildren() == 0);
    assert(N->getNumChildren() != 0 || Exits.count(N));
    for (auto *Ch: N->Children) {
        assert(Ch->Parents.count(N));
    }
    for (auto *Pa: N->Parents) {
        assert(Pa->Children.count(N));
    }
}

z3::expr SliceGraph::simplify(const z3::expr &Expr) const {
    if (Expr.is_const()) {
        return Expr;
    }

    auto ArgVec = Z3::vec();
    bool FindFree = false;
    for (auto I = 0; I < Expr.num_args(); ++I) {
        auto Arg = simplify(Expr.arg(I));
        if (Z3::is_free(Arg)) {
            FindFree = true;
        }
        ArgVec.push_back(Arg);
    }
    // todo we just select the first but we need to select a branch like phi
    if (Expr.is_ite() && Z3::is_free(ArgVec[0])) {
        return ArgVec[1];
    } else {
        assert(ArgVec.size() == Expr.num_args());
        if (Expr.is_and())
            return Z3::make_and(ArgVec);
        else if (Expr.is_or())
            return Z3::make_or(ArgVec);
        else if (FindFree)
            return Expr.is_bool() ? Z3::free_bool() : Z3::free_bv(Expr.get_sort().bv_size());
        auto Decl = Expr.decl();
        return Decl(ArgVec);
    }
}

void SliceGraph::postOrder(SliceGraphNode *N, std::set<SliceGraphNode *> &Visited, std::vector<SliceGraphNode *> &Ret) {
    if (Visited.count(N)) return;
    Visited.insert(N);

    for (auto *Ch: N->Children) {
        postOrder(Ch, Visited, Ret);
    }
    Ret.push_back(N);
}

void SliceGraph::postOrder(std::vector<SliceGraphNode *> &Ret) {
    std::set<SliceGraphNode *> Visited;
    for (auto *Entry: Entries) {
        postOrder(Entry, Visited, Ret);
    }
}

void SliceGraph::topoOrder(std::vector<SliceGraphNode *> &Ret) {
    std::map<SliceGraphNode *, unsigned> IndegreeMap;
    dfs([&IndegreeMap](SliceGraphNode *N) { IndegreeMap[N] = N->Parents.size(); });

    std::set<SliceGraphNode *> WorkList;
    for (auto *Entry: Entries) {
        WorkList.insert(Entry);
    }
    while (!WorkList.empty()) {
        auto *Begin = *WorkList.begin();
        WorkList.erase(Begin);
        Ret.push_back(Begin);

        // update indegree and worklist
        for (auto *Ch: Begin->Children) {
            auto XIt = IndegreeMap.find(Ch);
            assert(XIt != IndegreeMap.end());
            XIt->second--;
            if (XIt->second == 0) {
                WorkList.insert(Ch);
            }
        }
    }
    for (auto &It: IndegreeMap) {
        assert(!It.second);
    }
}

static std::vector<z3::expr> tryMerge(std::vector<std::vector<z3::expr>> &CondVec,
                                      unsigned F, unsigned T, unsigned Idx) {
    if (F == T) {
        if (Idx >= CondVec[F].size()) {
            return {};
        } else {
            std::vector<z3::expr> Vec;
            for (unsigned K = Idx; K < CondVec[F].size(); ++K) {
                Vec.push_back(CondVec[F][K]);
            }
            return {Z3::make_and(Vec)};
        }
    } else if (F > T) {
        return {};
    }

    assert(F < T);
    auto CommonWithNext = [&CondVec, Idx](unsigned I, unsigned T) {
        if (I <= T && I + 1 <= T) {
            if (Idx < CondVec[I].size() - 1 && Idx < CondVec[I + 1].size() - 1)
                return Z3::same(CondVec[I][Idx], CondVec[I + 1][Idx]);
        }
        return false;
    };

    unsigned I = F;
    while (CommonWithNext(I, T)) ++I;
    // [F, I]
    std::vector<z3::expr> X;
    X.push_back(CondVec[I][Idx]);
    auto Ret = tryMerge(CondVec, F, I, Idx + 1);
    X.insert(X.end(), Ret.begin(), Ret.end());
    // [I + 1, T]
    auto Y = tryMerge(CondVec, I + 1, T, Idx);

    if (X.empty())
        return std::move(Y);
    else if (Y.empty())
        return std::move(X);
    auto E1 = Z3::make_and(X);
    auto E2 = Z3::make_and(Y);
    X.clear();
    X.push_back(Z3::make_or(E1, E2));
    return std::move(X);
}

std::vector<z3::expr> SliceGraph::merge(std::vector<std::vector<z3::expr>> &PrevCondVec) {
    assert(!PrevCondVec.empty());
    if (PrevCondVec.size() == 1) {
        return PrevCondVec[0];
    }

    // dictionary order
    std::sort(PrevCondVec.begin(), PrevCondVec.end(),
              [](const std::vector<z3::expr> &A, const std::vector<z3::expr> &B) {
                  auto MinSize = std::min(A.size(), B.size());
                  for (unsigned I = 0; I < MinSize; ++I) {
                      auto AID = Z3::id(A[I]);
                      auto BID = Z3::id(B[I]);
                      if (AID < BID)
                          return true;
                      else if (AID > BID)
                          return false;
                  }
                  return A.size() < B.size();
              });

    return tryMerge(PrevCondVec, 0, PrevCondVec.size() - 1, 0);
}

z3::expr SliceGraph::pc() {
    // add a fake unified exit
    if (Exits.empty())
        return Z3::bool_val(true);
    SliceGraphNode *Exit = new SliceGraphNode(Z3::bool_val(true));
    for (auto *E: Exits) {
        E->addChild(Exit);
        Exit->addParent(E);
    }
    Exits.clear();
    Exits.insert(Exit);

    // compute the reverse post order vector
    std::vector<SliceGraphNode *> ReversePostOrder;
    postOrder(ReversePostOrder);
    std::reverse(ReversePostOrder.begin(), ReversePostOrder.end());

    // traverse the post order vector, when merging, pull the common prefix out
    typedef std::vector<z3::expr> PrevCondition;
    std::map<SliceGraphNode *, std::vector<PrevCondition>> InVec;
    for (auto *Entry: Entries) {
        auto &Vec = InVec[Entry];
        Vec.emplace_back();
        Vec.back().push_back(Z3::bool_val(true));
    }
    for (auto *Node: ReversePostOrder) {
        //errs()<< "node: "<< Node->getCondition() << " Entries.count(Node) = "<< Entries.count(Node)<<" . Node->getNumParents() = " << Node->getNumParents() << " InVec[Node].size() = "<<InVec[Node].size()<<"\n";
        // for(std::set<SliceGraphNode *>::const_iterator i = Node->parent_begin(); i!=Node->parent_end();i++){
        //     errs() << "parent node condition: " << (*i)->getCondition()<<"\n";
        // }
        assert(Entries.count(Node) || Node->getNumParents() == InVec[Node].size());
        auto &PrevCondVec = InVec[Node];
        PrevCondition PrevCond = merge(PrevCondVec);
        for (auto *Ch: Node->Children) {
            auto &ChInVec = InVec[Ch];
            ChInVec.push_back(PrevCond);
            ChInVec.back().push_back(Node->getCondition());
        }

        if (Node == ReversePostOrder.back()) {
            // the last node, we need return;
            assert(Node == Exit);
//            // @{
//            unsigned K = 0;
//            for (auto X: PrevCond) {
//                outs() << "[" << ++K << "] " << X << "\n";
//            }
//            // @}
            remove(Node, true);
            auto RetExpr = Z3::make_and(PrevCond);
            return RetExpr;
        }
    }
    llvm_unreachable("Error: we must return in the loop above!");
}

void SliceGraph::removeFrom(SliceGraphNode *N, std::set<SliceGraphNode *> &Removed) {
    if (Removed.count(N)) return;

    std::set<SliceGraphNode *> WorkList;
    for (auto *NCh: N->Children) {
        if (!Removed.count(N))
            WorkList.insert(NCh);
    }
    remove(N, false);
    Removed.insert(N);

    for (auto *Ch: WorkList) {
        if (Ch->getNumParents() == 0) {
            removeFrom(Ch, Removed);
        }
    }
}

SliceGraph *getDiff(SliceGraph *first_graph, SliceGraph *second_graph){
    std::set<SliceGraphNode *> diff_nodes;
    // make sure there is only one entry in each graph, "true"
    //errs()<<"print out the size of entries in first_graph: "<<(first_graph->getEntries()).size()<<"\n";
   // errs()<<"print out the size of entries in second_graph: "<<(second_graph->getEntries()).size()<<"\n";
    
    SliceGraphNode *first_entry = *(first_graph->getEntries().begin());
    SliceGraphNode *second_entry = *(second_graph->getEntries().begin());
    // in two queues, the same nodes are in the same order
    std::queue<SliceGraphNode *> first_nodes;
    std::queue<SliceGraphNode *> second_nodes;

    first_nodes.push(first_entry);//the "true" node
    SliceGraphNode * first_node, * second_node;
    second_nodes.push(second_entry);//the "true" node

    while(!first_nodes.empty() && !second_nodes.empty()){
        first_node = first_nodes.front();
        first_nodes.pop(); 
        second_node = second_nodes.front();
        second_nodes.pop();
        //errs()<<"correct here1\n";
        errs()<<"first_node condition: "<<first_node->getCondition()<<"\n";
        errs()<<"second_node condition: "<<second_node->getCondition()<<"\n";
        if(first_node->getCondition().to_string()==second_node->getCondition().to_string()){
            //errs()<<"correct here2\n";
            for(std::set<SliceGraphNode *>::const_iterator i = first_node->child_begin(); i!=first_node->child_end();i++){
                bool flag = false;
                //errs()<<"correct here3\n";
                for(std::set<SliceGraphNode *>::const_iterator ii = second_node->child_begin(); ii!=second_node->child_end();ii++){
                    if((*i)->getCondition().to_string()==(*ii)->getCondition().to_string()){
                        flag = true;
                        first_nodes.push(*i);
                        second_nodes.push(*ii);
                        break;
                    }
                    //errs()<<"correct here4\n";
                }
                if(flag==false){
                    errs()<<"the different node :"<<(*i)->getCondition()<<"\n";
                    errs()<<"step 00: print out the size of parent in the graph: "<<(*i)->getNumParents()<<"\n";
                    for(std::set<SliceGraphNode *>::const_iterator it = (*i)->parent_begin(); it!=(*i)->parent_end();it++){
                            errs() << "parent node condition: " << (*it)->getCondition()<<"\n";
                    }
                    diff_nodes.insert(*i);                 
                    errs()<<"insert diff_node success\n";
                }
            }
            
        }
        
    }
    errs()<<"diff_nodes set success~\n";
    auto *res_Graph = new SliceGraph;
    SliceGraphNode* res_node = first_entry->findmaxSubgraph(diff_nodes);
    res_Graph->getEntries().insert(res_node);
    for(auto* exit_node: res_node->find_exitschild()){
        res_Graph->getExits().insert(exit_node);
    }
    return res_Graph;  
}



