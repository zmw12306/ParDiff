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

#ifndef CORE_SYMBOLICEXECUTION_H
#define CORE_SYMBOLICEXECUTION_H

#include "Core/SymbolicExecutionTree.h"
#include "Core/SliceGraph.h"
#include "Support/PushPop.h"

using namespace llvm;

struct PhiPointer {
    unsigned PhiID;
    unsigned Selected;

    bool operator<(const PhiPointer &P) const {
        return PhiID < P.PhiID;
    }
};

class SymbolicExecution {
private:
    PushPopSet<PhiPointer> PhiSelectorStack;
    PushPopVector<SliceGraphNode *> BNFExecutionPath;
    PushPopSet<unsigned> NamedElementStack;
    PushPopVector<z3::expr> PathCondStack;
    std::map<unsigned, std::vector<unsigned>> PhiID2DupValIDMap;

public:
    static char ID;

    SymbolicExecution() {}

    ~SymbolicExecution() = default;

    SymbolicExecutionTree *run(const z3::expr &, SliceGraph &);

private:
    void doSymbolicExecutionDFS(SymbolicExecutionTreeNode *, SliceGraphNode *, std::vector<PhiPointer> &);

    z3::expr doSymbolicExecutionSimplify(const z3::expr &);

    z3::expr doSymbolicExecutionEliminateUselessNaming(const z3::expr &);

    z3::expr doSymbolicExecutionEliminatePhi(const z3::expr &);

    z3::expr doSymbolicExecutionEliminateConflict(const z3::expr &);

    void evaluatePhi(SliceGraphNode *, std::map<unsigned, std::vector<unsigned>> &);

    void findDupPhiVal(const z3::expr &);

    bool isDupPhiVal(unsigned PhiID, unsigned ValID);
};

#endif /* CORE_SYMBOLICEXECUTION_H */
