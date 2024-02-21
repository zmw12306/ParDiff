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
#include "Transform/MergeReturn.h"

#define DEBUG_TYPE "MergeReturn"

char MergeReturn::ID = 0;
static RegisterPass<MergeReturn> X(DEBUG_TYPE, "Merging multiple returns to one");

void MergeReturn::getAnalysisUsage(AnalysisUsage &AU) const {
}

bool unifyReturnBlocks(Function &F) {
    std::vector<BasicBlock *> ReturningBlocks;

    for (BasicBlock &I: F)
        if (isa<ReturnInst>(I.getTerminator()))
            ReturningBlocks.push_back(&I);

    if (ReturningBlocks.size() <= 1)
        return false;

    // Insert a new basic block into the function, add PHI nodes (if the function
    // returns values), and convert all the return instructions into
    // unconditional branches.
    BasicBlock *NewRetBlock = BasicBlock::Create(F.getContext(), "UnifiedReturnBlock", &F);

    PHINode *PN = nullptr;
    if (F.getReturnType()->isVoidTy()) {
        ReturnInst::Create(F.getContext(), nullptr, NewRetBlock);
    } else {
        // If the function doesn't return void... add a PHI node to the block...
        PN = PHINode::Create(F.getReturnType(), ReturningBlocks.size(), "UnifiedRetVal");
        NewRetBlock->getInstList().push_back(PN);
        ReturnInst::Create(F.getContext(), PN, NewRetBlock);
    }

    // Loop over all of the blocks, replacing the return instruction with an
    // unconditional branch.
    for (BasicBlock *BB: ReturningBlocks) {
        // Add an incoming element to the PHI node for every return instruction that
        // is merging into this new block...
        if (PN)
            PN->addIncoming(BB->getTerminator()->getOperand(0), BB);

        BB->getInstList().pop_back();  // Remove the return insn
        BranchInst::Create(NewRetBlock, BB);
    }

    return true;
}

bool MergeReturn::runOnModule(Module &M) {
    bool Changed = false;
    for (auto &F: M) {
        if (F.isDeclaration()) continue;
        auto Transformed = unifyReturnBlocks(F);
        if (!Changed && Transformed) Changed = Transformed;
    }
    return Changed;
}
