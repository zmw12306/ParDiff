#include <llvm/Support/CommandLine.h>
#include <llvm/Support/Debug.h>
#include "BNF/FSM.h"
#include "Support/Z3.h"

#define DEBUG_TYPE "FSM"

// Initialize static member variable
int FSMnode::nextID = 0;

//connect fsm to this fsm
void FSM::connectFSM(FSMRef fsm){
    //connect all the exits of the first FSM with all the entries of the second one
    if(this->allNodes.empty()){//the current FSM is empty and uninitialized
        this->allNodes = fsm->getallNodes();
        this->Entry = fsm->Entry;
        this->Exits = fsm->Exits;
        return;
    }
    if(fsm->allNodes.empty()){
        return;
    }

    for(auto& exit: this->Exits){     
        for(const auto &entry : fsm->Entry->transition) {
            exit->addTransition(entry);
        }      
    }
    //update Exits with the Exits in fsm
    this->Exits.clear(); 
    this->Exits.insert(fsm->Exits.begin(), fsm->Exits.end());
    this->allNodes.insert(fsm->allNodes.begin(), fsm->allNodes.end());
    this->deleteNode(fsm->Entry);

    //no need to add the other transitions in fsm into the original fsm because transition is static
    
}


void FSM::simplify(){//start from the entry node, combine the edges with the equivalent constraints and start node
    simplify_node(Entry);
}


void FSM::simplify_node(FSMnodeRef node){//start from node, combine the edges with the equivalent constraints and start node
    //step one: find equal state to merge:
    std::set<FSMnodeRef> delete_set;
    std::map<FSMnodeRef, z3::expr>::iterator it, it1;
    for (it = node->transition.begin(); it != node->transition.end(); ++it){
        it1 = it;
        it1++;
        if(delete_set.count(it->first))
            continue;
        for (; it1 != node->transition.end(); ++it1){
            if(it->first->id() == it1->first->id())
                continue;
            if(delete_set.count(it1->first))
                continue;
            z3::expr F1 = it->second;
            z3::expr F2 = it1->second;
            if(Z3Solver::check(F1!=F2)==z3::unsat){
               //merge_set[child.first].insert(child1.first);
               merge_node(it->first, it1->first);
               delete_set.insert(it1->first);
            }
        }
    }
    for(auto N: delete_set){
        deleteNode(N);
        node->deleteTransition(N);    
    }

    //step two: recursively simplify_node
    for(auto& child: node->transition) {
        simplify_node(child.first);
    } 
}


void FSM::merge_node(FSMnodeRef N1, FSMnodeRef N2){//merge N2 -> N1
    for(const auto &entry : N2->transition) {
        N1->addTransition(entry);
    }    
    //this->deleteNode(N2);
}


FSMRef FSM::getFSMfromProduction(Product *P){
    FSMRef f = std::make_shared<FSM>();
    if(P->getRHS().size()==1){// conjunction: B[..]L[]B[..]L[] or B[..]B[..]
        auto Conj = P->getRHS().front();
        for(unsigned J = 0; J < Conj.size(); ++J){
            auto *Item = Conj[J];
            if(auto *IItem = dyn_cast<Interval>(Item)){
                f->connectFSM(getFSMfromIndexRange(IItem->getFrom(), IItem->getTo(), P));
            }
            else if(auto *PItem = dyn_cast<Product>(Item)){
                FSMRef PFSM = FSM::getFSMfromProduction(PItem);              
                f->connectFSM(PFSM);
            }

       }
       return f;
    }

    else{// disjunction: L | L | L | ...
        std::set<FSMRef> VFSM;
        for (auto &Conjunction: P->getRHS()){// |
            auto *Item = Conjunction[0];
            FSMRef PFSM = FSM::getFSMfromRHS(Item);
            VFSM.insert(PFSM);
        }
        f = combineFSM(VFSM);
        return f;
    }
    
}


FSMRef FSM::getFSMfromRHS(RHSItem *Item){ //Interval or Product
    FSMRef PFSM;
    if(auto *PItem = dyn_cast<Product>(Item)){
        PFSM = FSM::getFSMfromProduction(PItem);
    }
    else{
        llvm_unreachable("Error : not Product!");
        PFSM = std::make_shared<FSM>();
        FSMnodeRef Pnode = std::make_shared<FSMnode>();
        PFSM->addnode(Pnode);
        PFSM->setentry(Pnode);
        PFSM->addexit(Pnode);
        
    }
    return PFSM;
}


FSMRef combineFSM(std::set<FSMRef> v){
    FSMRef f = std::make_shared<FSM>();
    FSMnodeRef start_node = std::make_shared<FSMnode>();//new a start entry node
    f->addnode(start_node);
    f->setentry(start_node);
    for(FSMRef fsm: v){
        for(const auto &entry : fsm->Entry->transition) {
            start_node->addTransition(entry);
        }
        for(auto &exit: fsm->Exits){
            f->addexit(exit);
        }
        f->allNodes.insert(fsm->allNodes.begin(), fsm->allNodes.end());
        f->deleteNode(fsm->Entry);
        //no need to add the other transitions in fsm into the original fsm because transition is static
    }
    return f;
}


FSMRef getFSMfromIndexRange(BoundRef From, BoundRef To, Product *P){
    FSMRef PFSM = std::make_shared<FSM>();
    errs()<<"from: "<<From<<"->to: "<<To<<"\n";
    z3::expr result = z3::mk_and(Bound::getexprwithIndex(From, P->getAssertions())).simplify();      
    if(!result.is_true()){
        errs()<<result<<"\n";
        PFSM->connectFSM(getFSMfromIndex(From, P,result));
    }
    if(From!=To){
        z3::expr result = z3::mk_and(Bound::getexprwithIndex(To, P->getAssertions())).simplify();      
        if(!result.is_true()){
            errs()<<result<<"\n";
            PFSM->connectFSM(getFSMfromIndex(To, P,result));
        }
    }
    return PFSM;
}

FSMRef getFSMfromIndex(BoundRef B, Product *P, z3::expr result){
    FSMRef PFSM = std::make_shared<FSM>();
    FSMnodeRef start_node = std::make_shared<FSMnode>();
    FSMnodeRef end_node = std::make_shared<FSMnode>();
    PFSM->addnode(start_node);
    PFSM->addnode(end_node);
    PFSM->setentry(start_node);
    PFSM->addexit(end_node); 
    // for(auto e: P->getAssertions()){
    //     errs()<<e<<"\n";
    // }
    start_node->addTransition(end_node, result);
    return PFSM;

}


FSMRef FSM::getFSM(BNFRef B){
    std::set<FSMRef> v;
    errs()<<"product size: "<<(B->Products).size()<<"\n";
    for(auto *P: B->Products){
        if(!(P->getLHS())){
            v.insert(FSM::getFSMfromProduction(P));
        }
    }
    assert(v.size()==1);//shouldn't have more than one start in our defined BNF
    return *(v.begin());
}


void bisimulation(FSMRef f1, FSMRef f2){
    bisimulation(f1, f2, f1->Entry, f2->Entry);
}

void bisimulation(FSMRef f1, FSMRef f2, FSMnodeRef n1, FSMnodeRef n2){
    //TODO
    std::set<FSMnodeRef> child_set;
    std::vector<std::pair<FSMnodeRef, FSMnodeRef>> bisim_pair;
    z3::expr_vector diff1 = Z3::vec();
    z3::expr_vector diff2 = Z3::vec();
    errs()<<"start new group:\n";
    for (const auto& child1: n1->transition){
        z3::expr x1 = child1.second;
        bool flag = false;
        for (const auto& child2: n2->transition){      
            z3::expr x2 = child2.second;
            if(Z3Solver::check(x1 != x2) == z3::unsat) {//find the same transition, continue to compare
                flag = true;
                child_set.insert(child2.first);
                bisim_pair.push_back(std::make_pair(child1.first, child2.first));
                //bisimulation(f1, f2, child1.first, child2.first);//continue to compare
                break;
            }
        }       
            if(!flag && (Z3Solver::check(x1) == z3::sat)){
            
            errs()<<"diff: in F1 not in F2:  while compair "<<"state_"<<n1->id()<<" and state_"<< n2->id()<< ": state_" << n1->id() << " -> state_"<<child1.first->id()<<":"<<x1 <<"\n";
            diff1.push_back(x1);
        }
    }
    for (const auto& child: n2->transition){
        if(!child_set.count(child.first) && (Z3Solver::check(child.second) == z3::sat)){
            
            errs()<<"diff: in F2 not in F1:  while compair "<<"state_"<<n1->id()<<" and state_"<< n2->id()<< ": state_" << n2->id()<< " -> state_"<<child.first->id()<<":"<<child.second<<"\n";
            diff2.push_back(child.second);
        }
    }
    for(auto &pair: bisim_pair){
        bisimulation(f1, f2, pair.first, pair.second);
    }
    //errs()<<"end new group:\n";
    //similarity(diff1, diff2);
}

raw_ostream &operator<<(raw_ostream &DotStream, const FSMRef &Machine) {
    auto DotState = [](FSMnodeRef State, raw_ostream &OS) {
        OS << "\tstate_" << State->id() << "[label=\"" << State->id() << "\"];\n";
        for (auto Ch: State->transition) {
            OS << "\tstate_" << State->id() << "->state_" << Ch.first->id()
               << "[label=\"" << Z3::to_string(Ch.second) << "\"];\n";
        }
        OS << "\n";
    };

    DotStream << "\n";
    DotStream << "digraph machine {\n";
    for (auto &N: Machine->getallNodes()) {
        DotState(N, DotStream);
    }
    DotStream << "}\n";
    return DotStream;
}

int equal_AndOp( z3::expr_vector AndOps1,  z3::expr_vector AndOps2){
    int x = 0;
    for(auto AndOp1: AndOps1){
        for(auto AndOp2: AndOps2){
            if(Z3Solver::check(AndOp1 != AndOp2) == z3::unsat){
                x++;
                break;
            }
        }
    }
    return x;
}

void similarity(z3::expr_vector diff1, z3::expr_vector diff2){
    
    for(auto Expr1: diff1){
        z3::expr_vector AndOps1 = Z3::find_consecutive_ops(Expr1, Z3_OP_AND);
        int sim = 0;
        z3::expr match = Z3::bool_val(false);
        for(auto Expr2: diff2){
            if(Z3Solver::check(Expr1 == Expr2) == z3::unsat)
                continue;
            z3::expr_vector AndOps2 = Z3::find_consecutive_ops(Expr2, Z3_OP_AND);
            if(equal_AndOp(AndOps1, AndOps2) > sim){
                sim = equal_AndOp(AndOps1, AndOps2);
                match = Expr2;
            }           
        }
        if(sim > (diff1.size()/2)){
             errs()<<"match F1: "<< Expr1 << "with F2: "<< match <<"\n";
        }
    }

}



