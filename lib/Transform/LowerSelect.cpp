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
#include "Transform/LowerSelect.h"

#define DEBUG_TYPE "LowerSelect"

char LowerSelect::ID = 0;
static RegisterPass<LowerSelect> X(DEBUG_TYPE, "Converting select to if/else");

void LowerSelect::getAnalysisUsage(AnalysisUsage &AU) const {
}

static void transform(Instruction *Select) {
    auto *Function = Select->getFunction();
    auto *BranchBB = Select->getParent();

    // Note that all instructions BEFORE the specified iterator
    // stay as part of the original basic block, an unconditional branch is added
    // to the original BB, and the rest of the instructions in the BB are moved
    // to the new BB, including the old terminator.  The newly formed basic block
    // is returned. This function invalidates the specified iterator.
    BasicBlock *PhiBB = Select->getParent()->splitBasicBlock(Select, "");

    auto *TrueBB = BasicBlock::Create(Select->getContext(), "", Function, PhiBB);
    BranchInst::Create(PhiBB, TrueBB);
    auto *FalseBB = BasicBlock::Create(Select->getContext(), "", Function, PhiBB);
    BranchInst::Create(PhiBB, FalseBB);

    BranchBB->getTerminator()->eraseFromParent();
    BranchInst::Create(TrueBB, FalseBB, Select->getOperand(0), BranchBB);

    auto *Phi = PHINode::Create(Select->getType(), 2, "", Select);
    Phi->addIncoming(Select->getOperand(1), TrueBB);
    Phi->addIncoming(Select->getOperand(2), FalseBB);
    Select->replaceAllUsesWith(Phi);
    Select->eraseFromParent();
}

bool LowerSelect::runOnModule(Module &M) {
    std::vector<SelectInst *> Selects;
    for (auto &F: M) {
        for (auto &B: F) {
            for (auto &I: B) {
                if (I.getType()->isPointerTy()) continue;
                if (auto *SI = dyn_cast<SelectInst>(&I)) {
                    Selects.push_back(SI);
                }
            }
        }
    }
    if (Selects.empty()) return false;

    for (auto *Select: Selects)
        transform(Select);

    if (verifyModule(M, &errs())) {
        llvm_unreachable("Error: Lowerselect fails...");
    }
    return true;
}

