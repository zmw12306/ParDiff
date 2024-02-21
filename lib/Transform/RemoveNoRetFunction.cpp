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
#include "Transform/RemoveNoRetFunction.h"

#define DEBUG_TYPE "RemoveNoRetFunction"

char RemoveNoRetFunction::ID = 0;
static RegisterPass<RemoveNoRetFunction> X(DEBUG_TYPE, "removing a function that never returns");

void RemoveNoRetFunction::getAnalysisUsage(AnalysisUsage &AU) const {
}

bool RemoveNoRetFunction::runOnModule(Module &M) {
    for (auto &F: M) {
        if (F.doesNotReturn()) {
            F.deleteBody();
            F.setComdat(nullptr);
        }
    }
    return false;
}
