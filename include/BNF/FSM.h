#ifndef BNF_FSM_H
#define BNF_FSM_H

#include <llvm/Support/Casting.h>
#include <llvm/Support/Debug.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/ADT/StringRef.h>
#include "Support/Z3.h"
#include "BNF/BNF.h"
#include "BNF/Bound.h"
#include "BNF/Bound.h"
#include <vector>
#include <deque>
#include <set>
#include <unordered_set>

using namespace llvm;
#define BYTE_ARRAY "B"
class FSMnode;
class FSM;

typedef std::shared_ptr<FSM> FSMRef;
typedef std::shared_ptr<FSMnode> FSMnodeRef;

class FSMnode{
private:
    static int nextID;
    int ID;

public:
    std::map<FSMnodeRef, z3::expr> transition;

public:
    FSMnode() : ID(nextID++) {}

    int id() const { return ID; }

    void addTransition(std::pair<FSMnodeRef, z3::expr> x){
        transition.insert(x);
    }

    void addTransition(FSMnodeRef n, z3::expr exp){
        transition.insert({n, exp});
    }

    void deleteTransition(FSMnodeRef N){
        transition.erase(N);
    }
};

class FSM {
public:
    std::set<FSMnodeRef> allNodes;
    FSMnodeRef Entry;
    std::set<FSMnodeRef> Exits;
public:

    static FSMRef getFSMfromRHS(RHSItem *RHS);//transfer B[][] to a FSM

    static FSMRef getFSMfromProduction(Product *product);//transfer production to a FSM

    static FSMRef getFSM(BNFRef B);//transfer an entire bnf into FSM

    void setentry(FSMnodeRef n){
        Entry = n;
    }

    void addexit(FSMnodeRef n){
        Exits.insert(n);
    }

    std::set<FSMnodeRef> getallNodes(){
        return allNodes;
    }

    void addnode(FSMnodeRef n){
        allNodes.insert(n);
    }

    void deleteNode(FSMnodeRef n){
        allNodes.erase(n);
    }

    void merge_node(FSMnodeRef N1,FSMnodeRef N2);

    void deleteexit(FSMnodeRef n){
        Exits.erase(n);
    }

    void connectFSM(FSMRef fsm);// FSM1 -> FSM2

    void simplify();

    void simplify_node(FSMnodeRef node);

public:
    friend raw_ostream &operator<<(llvm::raw_ostream &, const FSMRef &);
};

FSMRef combineFSM(std::set<FSMRef> v);//conbine a vector of FSM into a entire FSM and return
FSMRef getFSMfromIndexRange(BoundRef From, BoundRef To, Product *P);//get the range[start, end] of a production into a FSM
FSMRef getFSMfromIndex(BoundRef B, Product *P, z3::expr result);//get the B[B] related constraints of a production into a FSM
void bisimulation(FSMRef f1, FSMRef f2);//compare two FSMs using bisimulation
void bisimulation(FSMRef f1, FSMRef f2, FSMnodeRef n1, FSMnodeRef n2);
int equal_AndOp( z3::expr_vector AndOps1,  z3::expr_vector AndOps2);
void similarity(z3::expr_vector diff1, z3::expr_vector diff2);

raw_ostream &operator<<(llvm::raw_ostream &, const FSMRef &);

#endif //BNF_FSM_H