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

#include <llvm/Support/CommandLine.h>
#include <map>
#include <set>
#include <vector>
#include "Core/SliceGraph.h"
#include "BNF/BNF.h"
#include <iostream> 
#include <string> 
#include "Support/ADT.h"

#define DEBUG_TYPE "BNF"

static cl::opt<bool> SimplifyBNF("pardiff-simplify-bnf", cl::desc("simplify bnf"), cl::init(true));
extern std::map<Product*, std::pair<std::string,std::string>> res_map1,res_map2;
extern std::map<Product*, BoundRef> To_map1, To_map2;
class BoundVec {
public:
    z3::expr Op;
    std::vector<BoundRef> Vec;
    std::vector<BoundRef> MinVec;
    std::vector<BoundRef> MaxVec;

public:
    BoundVec(const z3::expr &Op) : Op(Op) {}

    void push_back(const BoundRef &BR) {
        Vec.push_back(BR);
        if (MinVec.empty()) {
            MinVec.push_back(BR);
        } else {
            bool NeedAdd = false;
            for (unsigned I = 0; I < MinVec.size(); ++I) {
                auto PossibleMin = MinVec[I];
                bool LessThan = false;
                try {
                    LessThan = BR < PossibleMin;
                } catch (const std::runtime_error &) {
                    // not comparable, we need regard it as a min
                    NeedAdd = true;
                }
                if (LessThan) {
                    NeedAdd = true;
                    MinVec[I] = MinVec.back();
                    MinVec.pop_back();
                    --I;
                }
            }
            if (NeedAdd) MinVec.push_back(BR);
        }
        if (MaxVec.empty()) {
            MaxVec.push_back(BR);
        } else {
            bool NeedAdd = false;
            for (unsigned I = 0; I < MaxVec.size(); ++I) {
                auto PossibleMax = MaxVec[I];
                bool GreaterThan = false;
                try {
                    GreaterThan = BR > PossibleMax;
                } catch (const std::runtime_error &) {
                    // not comparable, we need regard it as a min
                    NeedAdd = true;
                }
                if (GreaterThan) {
                    NeedAdd = true;
                    MaxVec[I] = MaxVec.back();
                    MaxVec.pop_back();
                    --I;
                }
            }
            if (NeedAdd) MaxVec.push_back(BR);
        }
    }

    BoundRef &back() { return Vec.back(); }

    std::vector<BoundRef>::iterator begin() { return Vec.begin(); }

    std::vector<BoundRef>::iterator end() { return Vec.end(); }

    BoundRef &operator[](unsigned I) { return Vec[I]; }

    const BoundRef &operator[](unsigned I) const { return Vec[I]; }

    size_t size() const { return Vec.size(); }
};

typedef std::shared_ptr<BoundVec> BoundVecRef;

BoundVecRef createBoundRefVecRef(const z3::expr &Op) {
    z3::expr_vector Selects = Z3::find_all(Op, false, [](const z3::expr &E) {
        return E.decl().decl_kind() == Z3_OP_SELECT;
    });
    auto Ret = std::make_shared<BoundVec>(Op);
    for (auto Select: Selects)
        Ret->push_back(Bound::createBound(Select.arg(1)));
    return Ret;
}

static void merge(BoundVecRef Src, BoundVecRef Dst) {
    z3::expr_vector SrcOrOps = Z3::find_consecutive_ops(Src->Op, Z3_OP_OR);
    z3::expr_vector DstOrOps = Z3::find_consecutive_ops(Dst->Op, Z3_OP_OR);

    if (SrcOrOps.size() == 1 && DstOrOps.size() == 1) {
        Dst->Op = SrcOrOps[0] && DstOrOps[0];
    } else {
        z3::expr_vector OrVec = Z3::vec();
        for (auto S: SrcOrOps) {
            for (auto D: DstOrOps) {
                OrVec.push_back(S && D);
            }
        }
        Dst->Op = Z3::make_or(OrVec);
    }

    for (int K = 0; K < Src->size(); ++K) Dst->push_back((*Src)[K]);
}

RHSItem::~RHSItem() = default;

Product::Product(const z3::expr &Expr, BNF *NF) : RHSItem(RK_Product), Assertions(Z3::vec()) {
    static unsigned LHSCounter = 0;
    if(flag_for){
        LHSCounter = 0;
        flag_for = false;
    }
    LHS = LHSCounter++;

    if (Expr.is_or()) {
        z3::expr_vector OrOps = Z3::find_consecutive_ops(Expr, Z3_OP_OR);
        unsigned NA = OrOps.size();
        for (int I = 0; I < NA; ++I) {
            auto *Prod = new Product(OrOps[I], NF);
            RHS.emplace_back();
            RHS.back().emplace_back(Prod);
            NF->add(Prod);
        }
    } else {
        std::vector<BoundVecRef> Indices;
        {
            z3::expr_vector AndOps = Z3::find_consecutive_ops(Expr, Z3_OP_AND);
            for (auto Op: AndOps) {
                Indices.emplace_back(createBoundRefVecRef(Op));
            }
            assert(!Indices.empty());
            std::sort(Indices.begin(), Indices.end(), [](const BoundVecRef &A, const BoundVecRef &B) {
                // should be always comparable, and if there are multiple min,
                // the comparative result should be always the same
                return *A->MinVec.begin() < *B->MinVec.begin();
            });

            LLVM_DEBUG(for (auto &Vec: Indices) {
                unsigned K = 0;
                for (auto Ex: *Vec) {
                    if (K++ == 0) dbgs() << *Ex << "\nindexes: ";
                    else dbgs() << *Ex << ", ";
                }
                dbgs() << "\n--------\n";
            });
        }

        RHS.emplace_back();
        auto &ConjunctiveVec = RHS.back();
        int PrevIndicesIt = -1;
        int IndicesIt = 0;
        while (IndicesIt != Indices.size()) {
            if (PrevIndicesIt != -1) {
                // we need to check if comparable,
                // if nothing comparable,
                // it means that there is some violation of path conditions,
                // thus, just drop CurrVec.
                auto &CurrVec = Indices[IndicesIt];
                auto &PrevVec = Indices[PrevIndicesIt];
                if (!ADT::exists(CurrVec->MinVec, PrevVec->MaxVec,
                                 [](const BoundRef &A, const BoundRef B) {
                                     try {
                                         (void) (A < B); // check if comparable
                                         return true;
                                     } catch (const std::runtime_error &Err) {
                                         return false;
                                     }
                                 })) {
                    IndicesIt++;
                    continue;
                }
            }
            PrevIndicesIt = IndicesIt;

            auto CurrVecFrom = IndicesIt;
            auto CurrVecTo = CurrVecFrom;
            auto &CurrVec = Indices[IndicesIt++];
            if (IndicesIt != Indices.size()) {
                auto *NextVec = &Indices[IndicesIt];
                while (ADT::exists((*NextVec)->MinVec, CurrVec->MaxVec,
                                   [](const BoundRef &A, const BoundRef B) {
                                       try {
                                           return A <= B;
                                       } catch (const std::runtime_error &Err) {
                                           return false;
                                       }
                                   })) {
                    merge(*NextVec, CurrVec);
                    IndicesIt++;
                    CurrVecTo++;
                    if (IndicesIt != Indices.size()) {
                        NextVec = &Indices[IndicesIt];
                    } else {
                        break;
                    }
                }
            }

            auto WholeExpr = CurrVec->Op;
            if (WholeExpr.is_or()) {
                auto *Prod = new Product(WholeExpr, NF);
                NF->add(Prod);
                ConjunctiveVec.push_back(Prod);
            } else {
                std::sort(CurrVec->begin(), CurrVec->end(), [](const BoundRef &A, const BoundRef &B) {
                    // should always comparable
                    return A < B;
                });
                for (int K = 0; K < CurrVec->size(); ++K) {
                    auto Index = (*CurrVec)[K];
                    if (K > 0) {
                        auto Prev = (*CurrVec)[K - 1];
                        if (Prev == Index) {
                            continue;
                        } else if (Prev + 1 != Index) {
                            // padding middle
                            ConjunctiveVec.push_back(new Interval(Prev + 1, Index - 1));
                        }
                    }
                    ConjunctiveVec.push_back(new Interval(Index, Index));
                }
                Assertions.push_back(WholeExpr);
            }
        }
    }
}


BNF::BNF(const z3::expr &Expr) {
    //errs()<<"p******rint the PC from BNF generate: \n";
    //errs()<<Expr<<"\n";
    add(new Product(Expr, this));
    pad();
    if (SimplifyBNF.getValue()) simplify();
}

BNF::~BNF() {
    for (auto *P: Products) P->releaseMemory();
    for (auto *P: FalseProducts) P->releaseMemory();
    for (auto *P: Products) delete P;
    for (auto *P: FalseProducts) delete P;
}


SliceGraph *getGraph(BNFRef B){
    auto *Graph =new SliceGraph;
    //errs()<<"****print out the size of productions: "<<B->Products.size()<<"\n";
    for(auto *P: B->Products){
        if(!(P->getLHS())){
            errs()<<"find the one\n";
            errs()<<getProduct(*P)->getCondition()<<"\n";
            Graph->getEntries().insert(getProduct(*P));
            break;         
        }
        
    }
    errs()<<"print out the size of entries: "<<(Graph->getEntries()).size()<<"\n";
    Graph->dfs_findexits();
    if(Graph->getExits().empty())
        errs()<<"no exit-------!!!!!!!!\n";
    // SliceGraphNode *Exit = new SliceGraphNode(Z3::bool_val(false));
    // for (auto *E: Graph->getExits()) {
    //     E->addChild(Exit);
    //     Exit->addParent(E);
    // }
    // Graph->getExits().clear();
    // Graph->getExits().insert(Exit); 
    return Graph;
}

SliceGraphNode *getProduct(Product &P){
    z3::expr_vector ExtraCond = Z3::vec();
    z3::expr_vector BeforeSubstitution = Z3::vec();
    z3::expr_vector AfterSubstitution = Z3::vec();
    std::vector<SliceGraphNode *> conjunction_list;
    std::vector<SliceGraphNode *> disjunction_list;
    //if (P.LHS) O << "L" << P.LHS << " := ";
    //else O << "S := ";
    int i =0;
    for (auto &Conjunction: P.getRHS()) {//|
        i++;
        BoundRef Last;
        errs()<<"-------"<<i<<"-------"<<Conjunction.size()<<"\n";
        for (unsigned J = 0; J < Conjunction.size(); ++J) {//&
            auto *Item = Conjunction[J];
            if (auto *PItem = dyn_cast<Product>(Item)) {
                errs() << "L" << PItem->getLHS()<<"\n";
                SliceGraphNode* child = getProduct(*PItem);
                if(Conjunction.size()>1)
                    conjunction_list.push_back(child);
                else{
                    disjunction_list.push_back(child);
                }
                //add n->node;
                //O << "L" << PItem->getLHS();
                Last.reset();
            } else if (auto *IItem = dyn_cast<Interval>(Item)) {
                auto From = IItem->getFrom();
                auto To = IItem->getTo();
                if (Last) {
                    auto NewIndexVar = Z3::index_var();
                    ExtraCond.push_back(NewIndexVar == Last->expr() + 1);
                    //ExtraCond.push_back(NewIndexVar == Z3::add(Last->expr(), 1));
                    Last = Bound::createBound(NewIndexVar);
                    BeforeSubstitution.push_back(From->expr());
                    AfterSubstitution.push_back(Last->expr());
                } else if (isa<SymbolicBound>(From.get())) {
                    auto NewIndexVar = Z3::index_var();
                    ExtraCond.push_back(NewIndexVar == From->expr());
                    Last = Bound::createBound(NewIndexVar);
                    BeforeSubstitution.push_back(From->expr());
                    AfterSubstitution.push_back(Last->expr());
                } else {
                    Last.reset();
                }
                errs() << "B[" << (Last ? Last : From);
                if (From == To) {
                    errs() << "]\n";
                } else {
                    if (isa<SymbolicBound>(To.get())) {
                        auto NewIndexVar = Z3::index_var();
                        ExtraCond.push_back(NewIndexVar == To->expr());
                        Last = Bound::createBound(NewIndexVar);
                        BeforeSubstitution.push_back(To->expr());
                        AfterSubstitution.push_back(Last->expr());
                    } else {
                        Last.reset();
                    }
                    errs() << ".." << (Last ? Last : To) << "]\n";
                }
            } else {
                llvm_unreachable("Error : unknown rhs type!");
            }

            if (J != Conjunction.size() - 1) {
                //errs() << " ";
            }
        }
        if (&Conjunction == &P.getRHS().back()) {
            //errs() << ";";
        } else {
            //errs() << " | ";
        }
    }
    
    
    SliceGraphNode* node, * nodee, *newnode;
    bool flag = true;
    if (!P.getAssertions().empty() || !ExtraCond.empty()) {
        for (auto Assert: P.getAssertions()) {
            z3::expr_vector ConjOps = Z3::find_consecutive_ops(Assert, Z3_OP_AND);
            for (auto ConjOp: ConjOps) {
                if (!ConjOp.is_true())
                    if(flag){
                        node = new SliceGraphNode(ConjOp.substitute(BeforeSubstitution, AfterSubstitution));
                        nodee = node;
                        flag = false;
                    }
                        
                        //O << "\n     assert(" << ConjOp.substitute(BeforeSubstitution, AfterSubstitution) << ")";
                    else{
                        newnode = new SliceGraphNode(ConjOp.substitute(BeforeSubstitution, AfterSubstitution));
                        if((newnode->getCondition()).to_string() != "true"){
                            node->addChild(newnode);
                            newnode->addParent(node);
                            node = newnode; 
                        }
                                   
                    }
                        
            }
        }
        for (auto Assert: ExtraCond) {
            if(flag){
                SliceGraphNode *node = new SliceGraphNode(Assert);
                nodee = node;
                flag = false;
            }
                
            else{
                newnode = new SliceGraphNode(Assert);
                if((newnode->getCondition()).to_string() != "true"){
                    node->addChild(newnode);
                    newnode->addParent(node);
                    node = newnode; 
                }

            }
                
            //O << "\n     assert(" << Assert << ")";
        }
    } else {//no assertion in this production
        errs() << "assert(true)";
        if (P.getLHS()) errs() << "L" << P.getLHS() << " := ";
        else errs() << "S := \n";
        node = new SliceGraphNode(Z3::bool_val(true));
        errs()<< node->getCondition().to_string()<<"----------print\n";
        nodee = node;

    }
    for(auto* con_node: conjunction_list){
        if((con_node->getCondition()).to_string() != "true"){
            node->addChild(con_node);
            con_node->addParent(node);
            node = con_node;
        }
        else{
            for(std::set<SliceGraphNode *>::const_iterator i = con_node->child_begin(); i!=con_node->child_end();i++){
                node->addChild(*i);
                (*i)->addParent(node);
            }
        }
    }
    for(auto* disj_node: disjunction_list){
        if((disj_node->getCondition()).to_string() != "true"){
            node->addChild(disj_node);
            disj_node->addParent(node);
        }
        else{
            for(std::set<SliceGraphNode *>::const_iterator i = disj_node->child_begin(); i!=disj_node->child_end();i++){
                node->addChild(*i);
                (*i)->addParent(node);
            }
        }
    }


    return nodee;
}

raw_ostream &operator<<(llvm::raw_ostream &O, const Product &P) {
    z3::expr_vector ExtraCond = Z3::vec();
    z3::expr_vector BeforeSubstitution = Z3::vec();
    z3::expr_vector AfterSubstitution = Z3::vec();

    if (P.LHS) O << "L" << P.LHS << " := ";
    else O << "S := ";
    for (auto &Conjunction: P.RHS) {//&&
        BoundRef Last;
        for (unsigned J = 0; J < Conjunction.size(); ++J) {
            auto *Item = Conjunction[J];
            if (auto *PItem = dyn_cast<Product>(Item)) {
                O << "L" << PItem->getLHS();
                Last.reset();
            } else if (auto *IItem = dyn_cast<Interval>(Item)) {
                auto From = IItem->getFrom();
                auto To = IItem->getTo();
                if (Last) {
                    auto NewIndexVar = Z3::index_var();
                    //ExtraCond.push_back(NewIndexVar == Last->expr() + 1);
                    ExtraCond.push_back(NewIndexVar == Z3::add(Last->expr(), 1));
                    Last = Bound::createBound(NewIndexVar);
                    BeforeSubstitution.push_back(From->expr());
                    AfterSubstitution.push_back(Last->expr());
                } else if (isa<SymbolicBound>(From.get())) {
                    auto NewIndexVar = Z3::index_var();
                    ExtraCond.push_back(NewIndexVar == From->expr());
                    Last = Bound::createBound(NewIndexVar);
                    BeforeSubstitution.push_back(From->expr());
                    AfterSubstitution.push_back(Last->expr());
                } else {
                    Last.reset();
                }
                O << "B[" << (Last ? Last : From);
                if (From == To) {
                    O << "]";
                } else {
                    if (isa<SymbolicBound>(To.get())) {
                        auto NewIndexVar = Z3::index_var();
                        ExtraCond.push_back(NewIndexVar == To->expr());
                        Last = Bound::createBound(NewIndexVar);
                        BeforeSubstitution.push_back(To->expr());
                        AfterSubstitution.push_back(Last->expr());
                    } else {
                        Last.reset();
                    }
                    O << ".." << (Last ? Last : To) << "]";
                }
            } else {
                llvm_unreachable("Error : unknown rhs type!");
            }

            if (J != Conjunction.size() - 1) {
                O << " ";
            }
        }
        if (&Conjunction == &P.RHS.back()) {
            O << ";";
        } else {
            O << " | ";
        }
    }

    if (!P.Assertions.empty() || !ExtraCond.empty()) {
        for (auto Assert: P.Assertions) {
            z3::expr_vector ConjOps = Z3::find_consecutive_ops(Assert, Z3_OP_AND);
            for (auto ConjOp: ConjOps) {
                if (!ConjOp.is_true())
                    O << "\n     assert(" << ConjOp.substitute(BeforeSubstitution, AfterSubstitution) << ")";
            }
        }
        for (auto Assert: ExtraCond) {
            O << "\n     assert(" << Assert << ")";
        }
    } else {
        O << "\n     assert(true)";
    }
    return O;
}

bool Product::nonTerminalDisjunction() const {
    bool Ret = true;
    for (auto &OneRHS: RHS) {
        assert(!OneRHS.empty());
        if (OneRHS.size() != 1 || !isa<Product>(OneRHS[0])) {
            Ret = false;
            break;
        }
    }
    return Ret;
}

bool Product::containsNonTerminal() const {
    for (auto &OneRHS: RHS) {
        for (auto *Item: OneRHS) {
            if (isa<Product>(Item))
                return true;
        }
    }
    return false;
}

raw_ostream &operator<<(llvm::raw_ostream &O, const BNFRef &B) {
    O << "\n<BNF>\n";
    bool First = true;
    unsigned NumAssertions = 0;
    for (auto *P: B->Products) {
        if (First) {
            O << "    " << *P << "\n";
            First = false;
        } else {
            O << "\n    " << *P << "\n";
        }
        NumAssertions += P->getNumAssertions();
    }
    O << "</BNF>\n";
    O << "\nTotal: " << B->Products.size() << " productions.";
    if (B->Products.size()) O << "\nAssertions/Production: " << NumAssertions / B->Products.size() << ".";
    return O;
}

z3::expr getPS(Product* P){
    z3::expr_vector res = Z3::vec();
    
    for(auto Assert: P->getAssertions()){
        res.push_back(Assert);
    }

    if(P->getRHS().size()==1){
    // conjunction: B[..]L[]B[..]L[] or B[..]B[..]
        auto Conj = P->getRHS().front();

        for(unsigned J = 0; J < Conj.size(); ++J){
            auto *Item = Conj[J];
            if(auto *PItem = dyn_cast<Product>(Item)){
                z3::expr sub_pc = getPS(PItem);
                res.push_back(sub_pc);
            }

        }
    }
    else{
    //disjunction: B[]||B[]||B[]
        z3::expr_vector OrVec = Z3::vec();
        for(auto &Conj: P->getRHS()){
             auto *Item = Conj[0];
             if(auto *PItem = dyn_cast<Product>(Item)){
                OrVec.push_back(getPS(PItem));
             }
        }
        res.push_back(z3::mk_or(OrVec).simplify());
    }
    z3::expr result = z3::mk_and(res).simplify();
    errs()<<"getPS result for Product: L"<<P->getLHS()<<":\n"<<result<<"\n";
    return result;
    

}


static void findMax(RHSItem *RHS, std::vector<BoundRef> &MaxVec) {
    if (auto *Prod = dyn_cast_or_null<Product>(RHS)) {
        for (auto It = Prod->rhs_begin(), E = Prod->rhs_end(); It != E; ++It) {
            findMax(It->back(), MaxVec);
        }
    } else if (auto *Int = dyn_cast_or_null<Interval>(RHS)) {
        auto CurrBoundRef = Int->getTo();
        if (MaxVec.empty()) {
            MaxVec.push_back(CurrBoundRef);
        } else {
            bool NeedAdd = false;
            for (unsigned I = 0; I < MaxVec.size(); ++I) {
                auto PossibleMax = MaxVec[I];
                if (CurrBoundRef > PossibleMax) { // must always comparable
                    NeedAdd = true;
                    MaxVec[I] = MaxVec.back();
                    MaxVec.pop_back();
                    --I;
                }
            }
            if (NeedAdd) MaxVec.push_back(CurrBoundRef);
        }
    } else {
        llvm_unreachable("Error: unknown RHS type!");
    }
}

void BNF::pad() {
    auto FirstProd = *Products.rbegin();
    padHead(FirstProd, Bound::createBound(0));
}

void BNF::padHead(Product *P, BoundRef Start) {
    for (auto &RHS: P->RHS) {
        if (RHS.empty()) continue;
        padHead(RHS[0], Start);

        for (unsigned K = 1; K < RHS.size(); ++K) {
            auto *PrevRHS = RHS[K - 1];
            auto *NextRHS = RHS[K];
            // if we have 2nd rhs, we need to pad the tail of the previous rhs
            // and determine the start boundref of the 2nd rhs
            std::vector<BoundRef> PrevMax;
            findMax(PrevRHS, PrevMax);
            assert(PrevMax.size() == 1);
            padTail(PrevRHS, PrevMax[0]);

            // pad the next
            padHead(NextRHS, PrevMax[0] + 1);
        }
    }
}

void BNF::padHead(RHSItem *RHS, BoundRef Start) {
    if (auto *Prod = dyn_cast_or_null<Product>(RHS)) {
        padHead(Prod, Start);
    } else if (auto *Int = dyn_cast_or_null<Interval>(RHS)) {
        Int->setFrom(Start);
    } else {
        llvm_unreachable("Error: unknown RHS type!");
    }
}

void BNF::padTail(RHSItem *RHS, BoundRef End) {
    if (auto *Prod = dyn_cast_or_null<Product>(RHS)) {
        for (auto It = Prod->rhs_begin(), E = Prod->rhs_end(); It != E; ++It) {
            padTail(It->back(), End);
        }
    } else if (auto *Int = dyn_cast_or_null<Interval>(RHS)) {
        Int->setTo(End);
    } else {
        llvm_unreachable("Error: unknown RHS type!");
    }
}

void BNF::simplify() {
    simplifyByCheckConflict(); // remove false products
    simplifyByMerge(); // merge some products
    simplifyByRemoveUnused(); // merge may lead to some unused products
    simplifyByMergeFieldName(); // merging the same field names
 }

 void BNF::simplifyByMergeFieldName() {
     for (auto *P: Products) {
         std::map<std::string, std::vector<z3::expr>> NameByteMap;
         for (auto E: P->Assertions) {
             if (Z3::is_naming_eq(E)) {
                 auto NameStrExpr = E.arg(1);
                 auto BytesExpr = E.arg(0).arg(0);
                 auto ByteV = Z3::find_consecutive_ops(BytesExpr, Z3_OP_CONCAT, false);
                 for (auto B: ByteV) {
                     if (B.decl().decl_kind() != Z3_OP_SELECT) continue;
                     NameByteMap[NameStrExpr.to_string()].push_back(B);
                 }
             }
         }

         auto It = NameByteMap.begin();
         while (It != NameByteMap.end()) {
             if (It->second.size() <= 1) {
                 It = NameByteMap.erase(It);
             } else {
                 ++It;
             }
         }

         for (unsigned K = 0; K < P->Assertions.size(); ++K) {
             auto E = P->Assertions[K];
             if (Z3::is_naming_eq(E)) {
                 auto NameStrExpr = E.arg(1);
                 if (NameByteMap.count(NameStrExpr.to_string())) {
                     auto Back = P->Assertions.back();
                     P->Assertions.set(K, Back);
                     P->Assertions.pop_back();
                     --K;
                 }
             }
         }

         for (auto &NIt: NameByteMap) {
             auto &Name = NIt.first;
             auto &Vec = NIt.second;
             std::sort(Vec.begin(), Vec.end(), [](const z3::expr &A, const z3::expr &B) {
                 assert(A.decl().decl_kind() == Z3_OP_SELECT);
                 assert(B.decl().decl_kind() == Z3_OP_SELECT);
                 return Z3::byte_array_element_index_less_than(A.arg(1), B.arg(1));
             });
             auto Naming = Z3::naming(Z3::byte_array_range(Vec.front().arg(0), Vec.front().arg(1), Vec.back().arg(1)),
                                      Name.c_str());
             P->Assertions.push_back(Naming);
         }
     }
}

void BNF::simplifyByMerge() {
    // L1 := L2 | L3;
    // L2 := L4 | L5
    // =>
    // L1 := L4 | L5 | L3
    for (auto *L1: Products) {
        for (auto It = L1->RHS.begin(); It != L1->RHS.end();) {
            auto &OneRHS = *It;
            if (OneRHS.size() == 1 && isa<Product>(OneRHS[0])) {
                auto *L2 = (Product *) OneRHS[0];
                if (L2->nonTerminalDisjunction()) {
                    for (auto &X: L2->RHS) {
                        L1->RHS.emplace_back(std::move(X));
                    }

                    It = L1->RHS.erase(It); // remove RHSProd from Prod's RHS
                    assert(L1 != L2);
                    continue;
                }
            }
            ++It;
        }
    }

    // L2 := *****
    // L1 := L2
    // =>
    // L3 := *****
    for (auto *L1: Products) {
        if (L1->RHS.size() == 1 && L1->RHS.back().size() == 1) {
            if (auto *L2 = dyn_cast<Product>(L1->RHS.back().back())) {
                L1->RHS = std::move(L2->RHS);
                L1->Assertions = L2->Assertions;
                assert(L2->RHS.empty());
            }
        }
    }
}

void BNF::simplifyByCheckConflict() {
    for (auto It = Products.begin(); It != Products.end();) {
        auto *P = *It;
        if (P->Assertions.empty()) {
            ++It;
            continue;
        }
        // pre-processing assertions
        auto AndExprOfAssert = Z3::make_and(P->Assertions);
        P->Assertions.resize(0);
        if (AndExprOfAssert.is_and()) {
            for (unsigned I = 0; I < AndExprOfAssert.num_args(); ++I) {
                P->Assertions.push_back(AndExprOfAssert.arg(I));
            }
        } else {
            P->Assertions.push_back(AndExprOfAssert);
        }

        // remove useless products; a product with only terminals but with only distinct in its assertions
        // do this before call z3::simplify, which will over-simplify the formulae and make the heuristics not work
        if (!P->containsNonTerminal()) {
            bool AllNe = true;
            if (AndExprOfAssert.is_and())
                for (unsigned I = 0; I < AndExprOfAssert.num_args(); ++I) {
                    if (!Z3::is_distinct_or_not_eq(AndExprOfAssert.arg(I))) {
                        AllNe = false;
                        break;
                    }
                }
            else AllNe = Z3::is_distinct_or_not_eq(AndExprOfAssert);
            if (AllNe) {
                P->Assertions.resize(0);
                P->Assertions.push_back(Z3::bool_val(false));

                It = Products.erase(It);
                FalseProducts.insert(P);
                continue;
            }
        }

        // compute simplified form, remove obviously infeasible product
        // and remove obviously unnecessary formulae
        auto SimplifiedAssert = Z3::simplify(P->Assertions);
        if (SimplifiedAssert.is_false()) {
            P->Assertions.resize(0);
            P->Assertions.push_back(SimplifiedAssert);

            It = Products.erase(It);
            FalseProducts.insert(P);
            continue;
        } else {
            P->Assertions = Z3::find_consecutive_ops(SimplifiedAssert, Z3_OP_AND);
            for (int I = 0; I < P->Assertions.size(); ++I) {
                auto Assert = P->Assertions[I];
                if (Assert.decl().decl_kind() == Z3_OP_NOT) {
                    auto SimplifiedForm = Z3::negation(Assert.arg(0));
                    P->Assertions.set(I, SimplifiedForm);
                }
            }
        }
        ++It;
    }

    auto Revisit = [this](Product *P) {
        auto &RHS = P->RHS;
        auto It = RHS.begin();
        while (It != RHS.end()) {
            auto &Conj = *It;
            bool False = false;
            for (auto *Item: Conj) {
                if (auto *PItem = dyn_cast<Product>(Item)) {
                    if (FalseProducts.count(PItem)) {
                        False = true;
                        break;
                    }
                }
            }
            if (False) {
                It = RHS.erase(It);
            } else {
                ++It;
            }
        }
        if (RHS.empty()) {
            return true;
        }
        return false;
    };

    // remove redundant products, because many have become false
    unsigned FalseProductOrgSize = FalseProducts.size();
    unsigned FalseProductNewSize = 0;
    while (FalseProductNewSize != FalseProductOrgSize) {
        FalseProductOrgSize = FalseProducts.size();
        for (auto It = Products.begin(); It != Products.end();) {
            auto *P = *It;
            if (Revisit(P)) {
                P->Assertions.resize(0);
                P->Assertions.push_back(Z3::bool_val(false));
                It = Products.erase(It);
                FalseProducts.insert(P);
                continue;
            }
            ++It;
        }
        FalseProductNewSize = FalseProducts.size();
    }
}

void BNF::simplifyByRemoveUnused() {
    // find unused product and remove
    std::map<Product *, unsigned> RefCountMap;
    for (auto *P: Products) {
        for (auto &RHS: P->RHS) {
            for (auto *Item: RHS) {
                if (auto *ProdItem = dyn_cast<Product>(Item)) {
                    auto It = RefCountMap.find(ProdItem);
                    if (It == RefCountMap.end()) {
                        RefCountMap[ProdItem] = 1;
                    } else {
                        It->second++;
                    }
                }
            }
        }
        if (P->getLHS() == 0) RefCountMap[P] = 1; // the start symbol
    }
    auto It = Products.begin();
    while (It != Products.end()) {
        auto *P = *It;
        auto RCIt = RefCountMap.find(P);
        if (RCIt != RefCountMap.end()) {
            assert(RCIt->second);
            It++;
        } else {
            for (auto &RHS: P->RHS) {
                for (auto *Item: RHS) {
                    if (auto *ProdItem = dyn_cast<Product>(Item)) {
                        auto ItemRCIt = RefCountMap.find(ProdItem);
                        assert(ItemRCIt != RefCountMap.end());
                        ItemRCIt->second--;
                        if (ItemRCIt->second == 0 && ProdItem != P) {
                            FalseProducts.insert(ProdItem);
                            Products.erase(ProdItem);
                        }
                    }
                }
            }
            FalseProducts.insert(P);
            It = Products.erase(It);
        }
    }
}

BNFRef BNF::get(const z3::expr &PC) {
    if (PC.is_false() || PC.is_true() || Z3::is_free(PC))
        return std::make_shared<BNF>();
    return std::make_shared<BNF>(PC);
}


BoundRef find_bound1(Product *P){
    errs()<<"hello\n";
    //P is the end,use res_map to get bound
    if(!To_map1.count(P)){
        errs()<<"P not exist in To_map\n";
        if(P->getRHS().size()==1){//&& conjunctions
            BoundRef end;
            auto conj = P->getRHS().front();
            auto* end_Item = conj[conj.size()-1];//the last item

            if(auto *PItem_end = dyn_cast<Product>(end_Item)){
                //end is -1
                if(res_map1[PItem_end].second == std::to_string(-1)){
                    To_map1[P] = Bound::createBound(-1);
                }
                else
                    To_map1[P] = find_bound1(PItem_end);             
            }
            else if(auto *IItem_end = dyn_cast<Interval>(end_Item)){
                //end is interval
                end = IItem_end->getTo();
                To_map1[P] = end;
            }
            else{
                llvm_unreachable("Error : unknown rhs type!");
            }
            //update sub_product
            for(unsigned J = 0; J < conj.size(); ++J){
                auto *Item = conj[J];
                if (auto *PItem = dyn_cast<Product>(Item)){
                    To_map1[PItem] = To_map1[P];
                    find_bound1(PItem);
                } 
                
            }
        }


        else{// || disjunctions
            if(res_map1[P].second == std::to_string(-1)){
                //the end are different
                To_map1[P] = Bound::createBound(-1);
                for(auto &conj: P->getRHS()){
                    auto *Item = conj[0];
                    if (auto *PItem = dyn_cast<Product>(Item)){
                       find_bound1(PItem);

                    }
                    else{
                        llvm_unreachable("Error : unreachable!");
                    }

                }

            }
            
            else{
                // all end are the same
                bool flag = false;           
                for(auto &conj: P->getRHS()){
                    auto *Item = conj[0];
                    if (auto *PItem = dyn_cast<Product>(Item)){
                        if(flag==false){
                            To_map1[P]=find_bound1(PItem);
                            flag = true;
                        }
                            
                        else{
                            To_map1[PItem] = To_map1[P];
                            find_bound1(PItem);
                        }
                            

                    }
                    else{
                        llvm_unreachable("Error : unreachable!");
                    }

                }


            } 
                
        }

    }


    //P isn't the end, deal with sub-products
    else{
        errs()<<"P exist in To_map\n";
        if(P->getRHS().size()==1){ //&
            auto conj = P->getRHS().front();
            for(unsigned J = 0; J < conj.size(); ++J){
                auto *Item = conj[J];
                if (auto *PItem = dyn_cast<Product>(Item)){
                    To_map1[PItem] = To_map1[P];
                    find_bound1(PItem);
                    
                }                
            }
        }
        // ||
        else{
            if(res_map1[P].second == std::to_string(-1)){
                //the end are different
                for(auto &conj: P->getRHS()){
                    auto *Item = conj[0];
                    if (auto *PItem = dyn_cast<Product>(Item)){
                       find_bound1(PItem);

                    }
                    else{
                        llvm_unreachable("Error : unreachable!");
                    }

                }

            }
            
            else{
                // all end are the same                     
                for(auto &conj: P->getRHS()){
                    auto *Item = conj[0];
                    if (auto *PItem = dyn_cast<Product>(Item)){
                    
                        To_map1[PItem] = To_map1[P];
                        find_bound1(PItem);
                                        
                    }
                    else{
                        llvm_unreachable("Error : unreachable!");
                    }

                }



            }

        }
    }              
      
    errs()<<"L"<<P->getLHS()<<" end: "<<To_map1[P]<<"\n";
    errs()<<"L"<<P->getLHS()<<"end analysis\n";
    return To_map1[P];
}

BoundRef find_bound2(Product *P){
    errs()<<"hello\n";
    //P is the end,use res_map to get bound
    if(!To_map1.count(P)){
        errs()<<"P not exist in To_map\n";
        if(P->getRHS().size()==1){//&& conjunctions
            BoundRef end;
            auto conj = P->getRHS().front();
            auto* end_Item = conj[conj.size()-1];//the last item

            if(auto *PItem_end = dyn_cast<Product>(end_Item)){
                //end is -1
                if(res_map2[PItem_end].second == std::to_string(-1)){
                    To_map2[P] = Bound::createBound(-1);
                }
                else
                    To_map2[P] = find_bound2(PItem_end);             
            }
            else if(auto *IItem_end = dyn_cast<Interval>(end_Item)){
                //end is interval
                end = IItem_end->getTo();
                To_map2[P] = end;
            }
            else{
                llvm_unreachable("Error : unknown rhs type!");
            }
            //update sub_product
            for(unsigned J = 0; J < conj.size(); ++J){
                auto *Item = conj[J];
                if (auto *PItem = dyn_cast<Product>(Item)){
                    To_map2[PItem] = To_map2[P];
                    find_bound2(PItem);
                } 
                
            }
        }


        else{// || disjunctions
            if(res_map2[P].second == std::to_string(-1)){
                //the end are different
                To_map2[P] = Bound::createBound(-1);
                for(auto &conj: P->getRHS()){
                    auto *Item = conj[0];
                    if (auto *PItem = dyn_cast<Product>(Item)){
                       find_bound2(PItem);

                    }
                    else{
                        llvm_unreachable("Error : unreachable!");
                    }

                }

            }
            
            else{
                // all end are the same
                bool flag = false;           
                for(auto &conj: P->getRHS()){
                    auto *Item = conj[0];
                    if (auto *PItem = dyn_cast<Product>(Item)){
                        if(flag==false){
                            To_map2[P]=find_bound2(PItem);
                            flag = true;
                        }
                            
                        else{
                            To_map2[PItem] = To_map2[P];
                            find_bound1(PItem);
                        }
                            

                    }
                    else{
                        llvm_unreachable("Error : unreachable!");
                    }

                }


            } 
                
        }

    }


    //P isn't the end, deal with sub-products
    else{
        errs()<<"P exist in To_map\n";
        if(P->getRHS().size()==1){ //&
            auto conj = P->getRHS().front();
            for(unsigned J = 0; J < conj.size(); ++J){
                auto *Item = conj[J];
                if (auto *PItem = dyn_cast<Product>(Item)){
                    To_map2[PItem] = To_map2[P];
                    find_bound2(PItem);
                    
                }                
            }
        }
        // ||
        else{
            if(res_map2[P].second == std::to_string(-1)){
                //the end are different
                for(auto &conj: P->getRHS()){
                    auto *Item = conj[0];
                    if (auto *PItem = dyn_cast<Product>(Item)){
                       find_bound2(PItem);

                    }
                    else{
                        llvm_unreachable("Error : unreachable!");
                    }

                }

            }
            
            else{
                // all end are the same                     
                for(auto &conj: P->getRHS()){
                    auto *Item = conj[0];
                    if (auto *PItem = dyn_cast<Product>(Item)){
                    
                        To_map2[PItem] = To_map2[P];
                        find_bound2(PItem);
                                        
                    }
                    else{
                        llvm_unreachable("Error : unreachable!");
                    }

                }



            }

        }
    }              
      
    errs()<<"L"<<P->getLHS()<<" end: "<<To_map2[P]<<"\n";
    errs()<<"L"<<P->getLHS()<<"end analysis\n";
    return To_map2[P];
}

void cmp_BNF (BNFRef &BNF1, BNFRef &BNF2){
    Product * S1 = *(--BNF1->Products.end());
    Product * S2= *(--BNF2->Products.end());
    cmp_product(S1, S2);
}

void cmp_product (Product * product1, Product * product2){
   errs()<<"\nProduct in the first version:\n";
    errs()<<*product1<<"\n";
    errs()<<"\nProduct in the second version:\n";
    errs()<<*product2<<"\n";
    if((product1->getRHS().size()==1)&&(product2->getRHS().size()==1)){
    // conjunction: B[..]L[]B[..]L[] or B[..]B[..]
        auto Conjunction1 = product1->getRHS().front();
        auto Conjunction2 = product2->getRHS().front();
        if(res_map1[product1].second != res_map2[product2].second){
            auto Item1 = Conjunction1[Conjunction1.size()-1];
            auto Item2 = Conjunction2[Conjunction2.size()-1];
            errs()<<"\nnot equal\n";
            if(res_map1[product1].second == std::to_string(-1)){
                if(auto *end1 = dyn_cast<Product>(Item1)){
                     errs()<<*end1<<"\n";
                     if(end1->getRHS().size()>1){
                        std::vector<Product *> m1;
                        for(auto &end1_Conj: end1->getRHS()){
                            auto *end1_Item1= end1_Conj[0];
                            if(auto *end1_PItem1 = dyn_cast<Product>(end1_Item1)){
                                if(res_map1[end1_PItem1].second != res_map2[product2].second){
                                    errs()<<"Not in F2:\n";
                                    errs()<<*end1_PItem1<<"\n";
                                }
                                else{
                                    //compare with that in product 2, but should first put into a set
                                    m1.push_back(end1_PItem1);
                                }
                            }
                        }
                    auto CondVec = Z3::vec();
                    for(auto prod1: m1){
                        auto product_CondVec = Z3::vec();
                        product_CondVec.push_back(getPS(prod1));
                        if(!To_map1.count(prod1)){
                            errs()<<"null here\n";
                        }
                        else if(isa<UpperBound>(To_map1[prod1].get())){
                            errs()<<"-1 upper bound here\n";
                        }
                        
                        else if(SymbolicBound *CB=dyn_cast<SymbolicBound>(To_map1[prod1].get())){
                            errs()<<"symbolic here\n";
                            errs()<<(CB->expr()).get_sort().bv_size()<<"\n";
                            product_CondVec.push_back(Z3::length()==Z3::trunc(CB->expr(), 32));
                            errs()<<"add symbolic success 3\n";
                        }
                        
                        else if(ConstantBound *SB = dyn_cast<ConstantBound>(To_map1[prod1].get())){
                            errs()<<"constant\n";
                            product_CondVec.push_back(Z3::length()==((int)SB->constant()+1));
                        }
                        
                        else{
                            errs()<<"other type\n";
                        }

                        CondVec.push_back(Z3::make_and(product_CondVec));
                             
                    }
                    cmp_Formula(Z3::make_or(CondVec), getPS(product2));

                  }
                }
            }
            else if(res_map2[product2].second == std::to_string(-1)){
                if(auto *end2 = dyn_cast<Product>(Item2)){
                     errs()<<*end2<<"\n";
                     if(end2->getRHS().size()>1){
                        std::vector<Product *> m2;
                        for(auto &end2_Conj: end2->getRHS()){
                            auto *end2_Item2= end2_Conj[0];
                            if(auto *end2_PItem2 = dyn_cast<Product>(end2_Item2)){
                                if(res_map1[end2_PItem2].second != res_map2[product1].second){
                                    errs()<<"Not in F1:\n";
                                    errs()<<*end2_PItem2<<"\n";
                                }
                                else{
                                    //compare with that in product 2, but should first put into a set
                                    m2.push_back(end2_PItem2);
                                }
                            }
                        }
                        auto CondVec = Z3::vec();
   
                         for(auto prod2: m2){
                            auto product_CondVec = Z3::vec();
                            product_CondVec.push_back(getPS(prod2));
                            if(!To_map2.count(prod2)){
                                errs()<<"null here\n";
                            }
                            else if(isa<UpperBound>(To_map2[prod2].get())){
                                errs()<<"-1 upper bound here\n";
                            }
                            
                            else if(SymbolicBound *CB=dyn_cast<SymbolicBound>(To_map2[prod2].get())){
                                errs()<<"symbolic here\n";
                                errs()<<(CB->expr()).get_sort().bv_size()<<"\n";
                                product_CondVec.push_back(Z3::length()==Z3::trunc(CB->expr(), 32));
                                errs()<<"add symbolic success 3\n";
                            }
                            
                            else if(ConstantBound *SB = dyn_cast<ConstantBound>(To_map2[prod2].get())){
                                errs()<<"constant\n";
                                product_CondVec.push_back(Z3::length()==((int)SB->constant()+1));
                            }
                            
                            else{
                                errs()<<"other type\n";
                            }

                            CondVec.push_back(Z3::make_and(product_CondVec));
                                
                        }
                        cmp_Formula(getPS(product1), Z3::make_or(CondVec));


                     }
                }
            }
            else{
                errs()<<"the end ont equal in conjunction-format\n";
            }
            return;

        }
        
        for(unsigned J = 0; J < Conjunction1.size(); ++J){
            auto *Item1 = Conjunction1[J];
            auto *Item2 = Conjunction2[J];

            if(auto *PItem1 = dyn_cast<Product>(Item1)){
            // if conj1 is L[] and conj2 is L[]:    
                if(auto *PItem2 = dyn_cast<Product>(Item2)){
                    //before cmp_product, check product begin and end
                    auto From = res_map1[PItem1].first;               
                    auto To = res_map1[PItem1].second;
                    auto From2 = res_map2[PItem2].first;
                    auto To2 = res_map2[PItem2].second;

                    if(From!=From2){
                        errs()<<"unreachable: from not equal";
                    }
                    else{
                        auto CondVec = Z3::vec();
                        auto CondVec2 = Z3::vec();
                        if(To == To2){
                            // end equal=>direct compare the two productions
                            errs()<<"cmp_product(PItem1,PItem2)\n";              
                            cmp_product(PItem1,PItem2);
                        }
                        else{
                                //not equal, do some grouping
                            
                                // if(to<to2){
                                // //e.g. L1=B[2..4], L2=B[2...7]
                                //     CondVec.pushback(getPS(PItem1));
                                //     for(int sub_j = to +1; sub_j<= to2){
                                //         for(auto Assert: product1->getAssertions()){
                                //             z3::expr_vector ConjOps = Z3::find_consecutive_ops(Assert, Z3_OP_AND);
                                //             for (auto ConjOp: ConjOps) {
                                //                 if (!ConjOp.is_true()){
                                //                     std::string i_str = "B["+std::to_string(sub_j);
                                //                     i_str += std::string("]");
                                //                     std::string res = Z3::to_string(ConjOp,true);                                        
                                //                     if(res.find(i_str)!=std::string::npos){                  
                                //                         CondVec.push_back(ConjOp);                                 
                                //                     }
                                //                 }
                                        
                                //             }
                                
                                //         }

                                //     }
                                //     CondVec2.pushback(getPS(PItem2));
                                // }
                                // else(to>to2){
                                // //e.g. L1=B[2..7], L2=B[2...5]
                                //     CondVec.pushback(getPS(PItem1));
                                //     CondVec2.pushback(getPS(PItem2));
                                //     for(int sub_j = to2 +1; sub_j<= to){
                                //         for(auto Assert: product2->getAssertions()){
                                //             z3::expr_vector ConjOps = Z3::find_consecutive_ops(Assert, Z3_OP_AND);
                                //             for (auto ConjOp: ConjOps) {
                                //                 if (!ConjOp.is_true()){
                                //                     std::string i_str = "B["+std::to_string(sub_j);
                                //                     i_str += std::string("]");
                                //                     std::string res = Z3::to_string(ConjOp,true);                                        
                                //                     if(res.find(i_str)!=std::string::npos){                  
                                //                         CondVec.push_back(ConjOp);                                 
                                //                     }
                                //                 }
                                        
                                //             }
                                
                                //         }

                                //     }
                                // }
                                
                                // errs()<<"cmpFormula: "<<Z3::make_and(CondVec)<<"  with  "<<Z3::make_and(CondVec2)<<"\n";
                                // cmp_Formula(Z3::make_and(CondVec), Z3::make_and(CondVec2)); 
                
                            errs()<<"cmpFormula: "<< getPS(product1) <<"  with  "<<getPS(product2)<<"\n";
                            cmp_Formula(getPS(product1),getPS(product2));
                            break;
                        }
                       
                        }
                    

                    
                }
                else{
                   // TO DO: handle corner cases  
                   errs()<<"todo: not equal in syntax\n";
                }
            }
            else if(auto *IItem1 = dyn_cast<Interval>(Item1)){
            // if conj1 is B[..] and conj2 is B[..]
                if(auto *IItem2 = dyn_cast<Interval>(Item2)){
                    auto From = IItem1->getFrom();
                    auto To = IItem1->getTo();
                    auto From2 = IItem2->getFrom();
                    auto To2 = IItem2->getTo();
                    int from, to, from2, to2;
                    //errs()<<"bnf1 from "<<From<<" to "<<To<<"\n";
                    //errs()<<"bnf2 from "<<From2<<" to "<<To2<<"\n";
                    if(isa<SymbolicBound>(From.get())){
                        errs()<<"todo: start from sym\n";    
                    }
                    else{
                        if(ConstantBound* x = dyn_cast<ConstantBound>(From.get())){
                            from = x->constant(); 
                            
                        } 
                        if(ConstantBound* x = dyn_cast<ConstantBound>(From2.get())){
                            from2 = x->constant(); 
                        
                        }   
                        if(ConstantBound* x = dyn_cast<ConstantBound>(To.get())){
                            to = x->constant(); 
                            
                        } 
                        if(ConstantBound* x = dyn_cast<ConstantBound>(To2.get())){
                            to2 = x->constant(); 
                            
                        }       
                        
                        // z3::expr Cond= Z3::bool_val(true);
                        // z3::expr Cond2= Z3::bool_val(true);
                        auto CondVec = Z3::vec();
                        auto CondVec2 = Z3::vec();
                        for(int i = from;i<= to;i++){
                            for(auto Assert: product1->getAssertions()){
                                z3::expr_vector ConjOps = Z3::find_consecutive_ops(Assert, Z3_OP_AND);
                                for (auto ConjOp: ConjOps) {
                                    if (!ConjOp.is_true()){
                                        std::string i_str = "B["+std::to_string(i);
                                        i_str += std::string("]");
                                        //errs()<<"i_str "<<i_str<<"\n";      
                                        std::string res = Z3::to_string(ConjOp,true);
                                        //errs()<<res<<"\n";
                                       
                                        if(res.find(i_str)!=std::string::npos){                  
                                            CondVec.push_back(ConjOp);
                                            //errs()<<"find "<<i_str<<"\n";                    
                                            //Cond = Cond && ConjOp; //Z3::make_and(P->Assertions)                                   
                                        }

                                    }
                                        
                                }
                                
                            }
                            errs()<<"start check symbolic1: L"<<product1->getLHS()<<"\n";
                            if(To_map1.count(product1)<=0){
                                errs()<<"null here\n";
                            }
                            else if(isa<UpperBound>(To_map1[product1].get())){
                                errs()<<"-1 upper bound here\n";
                            }
                            else if(SymbolicBound *CB=dyn_cast<SymbolicBound>(To_map1[product1].get())){
                                errs()<<"symbolic here\n";
                                errs()<<(CB->expr()).get_sort().bv_size()<<"\n";
                                CondVec.push_back(Z3::length()==Z3::trunc(CB->expr(), 32));
                                errs()<<"add symbolic success 1\n";
                            }
                                
                            else if(ConstantBound *SB = dyn_cast<ConstantBound>(To_map1[product1].get())){
                                errs()<<"constant\n";
                                CondVec.push_back(Z3::length()==((int)SB->constant()+1));
                            }
                            else{
                                errs()<<"other type\n";
                            }
                            errs()<<"end check symbolic1\n";

                            errs()<<Z3::make_and(CondVec)<<"\n";

                            for(auto Assert: product2->getAssertions()){
                                z3::expr_vector ConjOps = Z3::find_consecutive_ops(Assert, Z3_OP_AND);
                                for (auto ConjOp: ConjOps) {
                                    if (!ConjOp.is_true()){
                                        std::string i_str = "B["+std::to_string(i);
                                        i_str += std::string("]");
                                        //errs()<<"i_str "<<i_str<<"\n";      
                                        std::string res = Z3::to_string(ConjOp,true);
                                        //errs()<<res<<"\n";
                                       
                                        if(res.find(i_str)!=std::string::npos){                  
                                            CondVec2.push_back(ConjOp);
                                            //errs()<<"find "<<i_str<<"\n";                    
                                               
                                        }

                                    }
                                        
                                }
                                
                            }
                            errs()<<"start check symbolic2: L"<<product2->getLHS()<<"\n";
                            if(!To_map2.count(product2)){
                                errs()<<"null here\n";
                            }
                            else if(isa<UpperBound>(To_map2[product2].get())){
                                errs()<<"-1 upper bound here\n";
                            }
                            else if(SymbolicBound *CB=dyn_cast<SymbolicBound>(To_map2[product2].get())){
                                errs()<<"symbolic here\n";
                                errs()<<(CB->expr()).get_sort().bv_size()<<"\n";
                                CondVec2.push_back(Z3::length()==Z3::trunc(CB->expr(), 32));
                                errs()<<"add symbolic success 2\n";
                            }
                                
                            else if(ConstantBound *SB = dyn_cast<ConstantBound>(To_map2[product2].get())){
                                errs()<<"constant\n";
                                CondVec2.push_back(Z3::length()==((int)SB->constant()+1));
                            }
                            else{
                                errs()<<"other type\n";
                            }


                            errs()<<"end check symbolic2\n";
                            errs()<<Z3::make_and(CondVec2)<<"\n";
                            errs()<<"cmpFormula: "<<Z3::make_and(CondVec)<<"  with  "<<Z3::make_and(CondVec2)<<"\n";
                            cmp_Formula(Z3::make_and(CondVec), Z3::make_and(CondVec2));  
                            
                        }
                                   
                    }
                   
                    
                }
                else{
                    errs()<<"todo: not equal in syntax\n";    
                }
            }
            else{
                llvm_unreachable("Error : unknown rhs type!");
            }
            
        }
    }
//***********disjuction

    else if((product1->getRHS().size()>1)&&(product2->getRHS().size()>1)){
       //errs()<<"disjunction\n"; 
    // disjunction: L[]|L[]|L[]
        std::map<std::pair<std::string,std::string>, std::vector<Product *>> m1,m2;
        for(auto &Conjunction1: product1->getRHS()){
            auto *Item1= Conjunction1[0];
            if(auto *PItem1 = dyn_cast<Product>(Item1)){
                m1[res_map1[PItem1]].push_back(PItem1);
            }
        }
        for(auto &Conjunction2: product2->getRHS()){
            auto *Item2= Conjunction2[0];
            if(auto *PItem2 = dyn_cast<Product>(Item2)){
                m2[res_map2[PItem2]].push_back(PItem2);
            }
        }
        
        for(auto pair: m1){
            auto CondVec = Z3::vec();
            auto CondVec2 = Z3::vec();
              
            errs()<<"\nstart compare:\n";
            if(pair.first.first == "-1" || pair.first.second == "-1"){
            //[-1, ] or [ ,-1]
                errs()<<"debug: check when bound are unsure\n";
                //continue;
            }
            errs()<<"Production in the first version:\n";
            
            for(auto pro: pair.second){
                errs()<<*pro<<"\n";
            }
            

            if(m2.count(pair.first)){
                errs()<<"\nProduction in the second version:\n";
                for(auto pro2: m2[pair.first]){
                    errs()<<*pro2<<"\n";
                }

                for(auto prod1: pair.second){
                    auto product_CondVec = Z3::vec();
                    product_CondVec.push_back(getPS(prod1));
                    if(!To_map1.count(prod1)){
                        errs()<<"null here\n";
                    }
                    else if(isa<UpperBound>(To_map1[prod1].get())){
                        errs()<<"-1 upper bound here\n";
                    }
                    
                    else if(SymbolicBound *CB=dyn_cast<SymbolicBound>(To_map1[prod1].get())){
                        errs()<<"symbolic here\n";
                        errs()<<(CB->expr()).get_sort().bv_size()<<"\n";
                        product_CondVec.push_back(Z3::length()==Z3::trunc(CB->expr(), 32));
                        errs()<<"add symbolic success 3\n";
                    }
                    
                    else if(ConstantBound *SB = dyn_cast<ConstantBound>(To_map1[prod1].get())){
                        errs()<<"constant\n";
                        product_CondVec.push_back(Z3::length()==((int)SB->constant()+1));
                    }
                    
                    else{
                        errs()<<"other type\n";
                    }

                    CondVec.push_back(Z3::make_and(product_CondVec));
                             
                }
                

                //product2
                for(auto prod2: m2[pair.first]){
                    auto product_CondVec2 = Z3::vec();
                    product_CondVec2.push_back(getPS(prod2));
                    // for(auto Assert: prod2->getAssertions()){
                    //     z3::expr_vector ConjOps = Z3::find_consecutive_ops(Assert, Z3_OP_AND);
                    //     for (auto ConjOp: ConjOps) {
                    //         if (!ConjOp.is_true()){                    
                    //             product_CondVec2.push_back(ConjOp);                                                                          
                    //         }

                    //     }
                                
                    // }
                    errs()<<"start check symbolic2: L"<<product2->getLHS()<<"\n";
                    if(!To_map2.count(product2)){
                        errs()<<"null here\n";
                    }
                    else if(isa<UpperBound>(To_map2[prod2].get())){
                        errs()<<"-1 upper bound here\n";
                    }
                    else if(SymbolicBound *CB=dyn_cast<SymbolicBound>(To_map2[prod2].get())){
                        errs()<<"symbolic here\n";
                        errs()<<(CB->expr()).get_sort().bv_size()<<"\n";
                        product_CondVec2.push_back(Z3::length()==Z3::trunc(CB->expr(),32));
                        errs()<<"add symbolic success 4\n";
                    }
                        
                    else if(ConstantBound *SB = dyn_cast<ConstantBound>(To_map2[prod2].get())){
                        errs()<<"constant\n";
                        product_CondVec2.push_back(Z3::length()==((int)SB->constant()+1));
                    }
                    else{
                        errs()<<"other type\n";
                    }
                    CondVec2.push_back(Z3::make_and(product_CondVec2));
                }
                
                
                errs()<<"\ncmpFormula: "<<Z3::make_or(CondVec)<<"  with  "<<Z3::make_or(CondVec2)<<"\n";
                cmp_Formula(Z3::make_or(CondVec), Z3::make_or(CondVec2));  

            }
            else{
                errs()<<"\nnot in F2---diff Here\n";

            }
                 
        } 
        for(auto pair2: m2){
            if(!m1.count(pair2.first)){
                errs()<<"\nnot in F1---diff Here\n";
                for(auto pro: pair2.second){
                    errs()<<*pro<<"\n";
            }
            }
        }

    
    }
    else{
        errs()<<"handle corner cases\n";
    }

}

void cmp_Formula(z3::expr F1, z3::expr F2){
    //errs()<<"hahha\n";
    //check whether F1 and F2 is semantically equal 
    if(Z3Solver::check(F1!=F2)==z3::unsat){
        errs()<<"equal\n";
        //F1==F2
        errs()<<F1<<" == "<<F2<<"\n";
        return;
    }else{
        errs()<<"not equal\n";
        errs()<<F1<<" != "<<F2<<"\n";
        errs()<<"try to get model for the expr: \n";     
        Z3Solver::getmodel(F1!=F2, F1, F2);

    }
   
}

