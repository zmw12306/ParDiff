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

#include <llvm/IR/Constants.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Support/Debug.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#include "Transform/RemoveDeadBlock.h"

#define DEBUG_TYPE "RemoveDeadBlock"

char RemoveDeadBlock::ID = 0;
static RegisterPass<RemoveDeadBlock> X(DEBUG_TYPE, "remove dead block, not sure why simplifycfg does not work");

void RemoveDeadBlock::getAnalysisUsage(AnalysisUsage &AU) const {
}

bool RemoveDeadBlock::runOnModule(Module &M) {
    std::vector<BasicBlock *> Block2Remove;
    std::set<BasicBlock *> Visited;
    std::set<BasicBlock *> SuccVec;

    for (auto &F: M) {
        Block2Remove.clear();
        for (auto &B: F) {
            if (pred_size(&B) == 0 && (&B != &F.getEntryBlock() || B.getSinglePredecessor() == &B)) {
                Block2Remove.push_back(&B);
            }
        }

        // do transitively remove
        Visited.clear();
        while (!Block2Remove.empty()) {
            auto *B = Block2Remove.back();
            Block2Remove.pop_back();
            if (Visited.count(B)) continue;
            Visited.insert(B);

            SuccVec.clear();
            for (auto It = succ_begin(B), E = succ_end(B); It != E; ++It) {
                SuccVec.insert(*It);
            }
            DeleteDeadBlock(B);

            for (auto *Succ : SuccVec) {
                if (pred_size(Succ) == 0 && (Succ != &F.getEntryBlock() || Succ->getSinglePredecessor() == Succ)) {
                    Block2Remove.push_back(Succ);
                }
            }
        }
    }

    if (verifyModule(M, &errs())) {
        llvm_unreachable("Error: RemoveDeadBlock fails...");
    }
    return false;
}