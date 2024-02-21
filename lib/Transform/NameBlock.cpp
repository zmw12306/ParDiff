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
#include "Transform/NameBlock.h"

#define DEBUG_TYPE "NameBlock"

char NameBlock::ID = 0;
static RegisterPass<NameBlock> X(DEBUG_TYPE, "Naming each block for dbg");

void NameBlock::getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesAll();
}

bool NameBlock::runOnModule(Module &M) {
    for (auto &F: M) {
        unsigned BI = 0;
        for (auto &B: F) {
            if (!B.hasName()) B.setName("B" + std::to_string(++BI));
        }
    }
    return false;
}