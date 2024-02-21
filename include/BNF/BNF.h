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

#ifndef BNF_BNF_H
#define BNF_BNF_H

#include <llvm/Support/Casting.h>
#include <llvm/Support/Debug.h>
#include <llvm/Support/raw_ostream.h>
#include <list>
#include <vector>
#include <map>
#include "Core/SliceGraph.h"
#include "BNF/Bound.h"
#include "Support/Z3.h"

using namespace llvm;

class BNF;

extern std::vector<z3::expr> graphsForDiff;

// extern SliceGraph graph1;
// extern SliceGraph graph2;
extern bool flag_for;

class RHSItem {
public:
    enum RHSKind {
        RK_Interval,
        RK_Product
    };

private:
    RHSKind Kind;

public:
    explicit RHSItem(RHSKind K) : Kind(K) {}

    virtual ~RHSItem() = 0;

    RHSKind getKind() const { return Kind; }
};

class Interval : public RHSItem {
private:
    BoundRef From;
    BoundRef To;

public:
    Interval(const BoundRef &F, const BoundRef &T) : RHSItem(RK_Interval), From(F), To(T) {}

    ~Interval() override = default;

    BoundRef getFrom() const { return From; }

    BoundRef getTo() const { return To; }

    void setFrom(BoundRef &F) { From = F; }

    void setTo(BoundRef &T) { To = T; }

public:
    static bool classof(const RHSItem *M) {
        return M->getKind() == RK_Interval;
    }
};

class Product : public RHSItem {
private:
    /// the id of this product, standing for a non-terminal symbol on the left-hand side of the product
    unsigned LHS;

    /// the right-hand side is a disjunction of multiple cases (std::list)
    /// each case is a sequence of RHSItem (std::vector)
    std::list<std::vector<RHSItem *>> RHS;

    /// the assertions associated with this product
    z3::expr_vector Assertions;

public:
    Product(const z3::expr &, BNF *);

    ~Product() override = default;

    void releaseMemory() {
        for (auto &Vec: RHS) for (auto *Item: Vec) if (!isa<Product>(Item)) delete Item;
    }

    void setLHS(unsigned L) { LHS = L; }

    unsigned getLHS() const { return LHS; }
    std::list<std::vector<RHSItem *>> getRHS(){return RHS;}

    z3::expr_vector getAssertions() {return Assertions;}

    std::list<std::vector<RHSItem *>>::const_iterator rhs_begin() const { return RHS.begin(); }

    std::list<std::vector<RHSItem *>>::const_iterator rhs_end() const { return RHS.end(); }

    friend raw_ostream &operator<<(llvm::raw_ostream &, const Product &);

    bool nonTerminalDisjunction() const;

    bool containsNonTerminal() const;

    unsigned getNumAssertions() const { return Assertions.size(); }

    
    
private:
    friend class BNF;

public:
    static bool classof(const RHSItem *M) {
        return M->getKind() == RK_Product;
    }
};

struct ProductLessThan {
    bool operator()(const Product *P1, const Product *P2) const {
        return P1->getLHS() > P2->getLHS();
    }
};

typedef std::shared_ptr<BNF> BNFRef;

class BNF {

public:
    std::set<Product *, ProductLessThan> Products;
    std::set<Product *> FalseProducts;

public:
    BNF() = default;

    explicit BNF(const z3::expr &);

    ~BNF();

    void add(Product *P) { Products.insert(P); }
    // SliceGraph *getGraph(const Product &P);
    
    

public:
    static BNFRef get(const z3::expr &PC);

private:
    void pad();

    void padHead(Product *, BoundRef);

    void padHead(RHSItem *, BoundRef);

    void padTail(RHSItem *, BoundRef);

    void simplify();

    void simplifyByCheckConflict();

    void simplifyByMerge();

    void simplifyByRemoveUnused();

    void simplifyByMergeFieldName();

    friend raw_ostream &operator<<(llvm::raw_ostream &, const BNFRef &);
};

raw_ostream &operator<<(llvm::raw_ostream &, const BNFRef &);

raw_ostream &operator<<(llvm::raw_ostream &, const Product &);

// raw_ostream &operator<<(llvm::raw_ostream &O, std::list<std::vector<RHSItem *>> RHS){
//     if(RHS)
// }

z3::expr getPS(Product* P);

SliceGraph *getGraph(BNFRef B);

SliceGraphNode *getProduct(Product &P);

//std::map<unsigned, Product *> getMap(BNFRef B); // map: LHS->Product *

BoundRef find_bound1(Product *P);

BoundRef find_bound2(Product *P);

void cmp_BNF (BNFRef &BNF1, BNFRef &BNF2);

void cmp_product (Product * product1, Product * product2);

void cmp_Formula(z3::expr F1, z3::expr F2);

void cmp_asserts();


#endif //BNF_BNF_H




