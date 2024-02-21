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


#ifndef CORE_EXECUTIONTREE_H
#define CORE_EXECUTIONTREE_H

#include <set>
#include <vector>
#include "Support/Z3.h"

class SymbolicExecutionTreeNode {
    friend class SymbolicExecutionTree;

private:
    z3::expr Expr;
    SymbolicExecutionTreeNode *Parent = nullptr;
    std::set<SymbolicExecutionTreeNode *> Children;

public:
    SymbolicExecutionTreeNode() : Expr(Z3::bool_val(true)) {}

    SymbolicExecutionTreeNode(const z3::expr &E) : Expr(E) {}

    z3::expr getExpr() const { return Expr; }

    void setExpr(const z3::expr &E) { Expr = E; }

    void addChild(SymbolicExecutionTreeNode *);

    SymbolicExecutionTreeNode *getParent() const { return Parent; }
};

class SymbolicExecutionTree {
private:
    SymbolicExecutionTreeNode *Root;

public:
    SymbolicExecutionTree(SymbolicExecutionTreeNode *Rt) : Root(Rt) {}

    ~SymbolicExecutionTree();

    void simplify();

    void dot(std::string &File, const char * = "") const;

    z3::expr pc() const;

private:
    void compressInfeasiblePaths();

    void compressOffsprings();

    void compressSiblings();

    z3::expr pc(SymbolicExecutionTreeNode *) const;

public:
    template<class ActionAtDFS>
    void dfs(ActionAtDFS Act) const {
        std::vector<SymbolicExecutionTreeNode *> Stack;
        std::set<SymbolicExecutionTreeNode *> Visited;
        Stack.push_back(Root);
        while (!Stack.empty()) {
            auto *Top = Stack.back();
            Stack.pop_back();
            if (Visited.count(Top)) continue;
            Visited.insert(Top);

            Act(Top);

            for (auto *Ch: Top->Children) {
                Stack.push_back(Ch);
            }
        }
    }
};

#endif //CORE_EXECUTIONTREE_H
