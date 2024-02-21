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

#include <llvm/IR/Instructions.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/Debug.h>
#include <llvm/Support/Format.h>
#include "Core/DomInformationAnalysis.h"

#define DEBUG_TYPE "DomInformationAnalysis"

using namespace llvm;

char DomInformationAnalysis::ID = 0;
static RegisterPass<DomInformationAnalysis> X(DEBUG_TYPE, "A module pass of dom info");

DomInformationAnalysis::~DomInformationAnalysis() {
    for (auto &It: DomInfoMap) {
        delete It.second;
    }
}

void DomInformationAnalysis::getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesAll();
    AU.addRequired<DominatorTreeWrapperPass>();
}

bool DomInformationAnalysis::runOnModule(Module &M) {
    return false;
}

FunctionDomInformation *DomInformationAnalysis::getDomInfo(Function &F) {
    if (F.empty()) return nullptr;
    auto It = DomInfoMap.find(&F);
    if (It != DomInfoMap.end()) return It->second;
    auto *DT = &getAnalysis<DominatorTreeWrapperPass>(F).getDomTree();
    auto *FDI = new FunctionDomInformation(&F, DT);
    DomInfoMap[&F] = FDI;
    return FDI;
}

FunctionDomInformation::FunctionDomInformation(Function *F, DominatorTree *DT) : F(F) {
    for (auto &B: *F) {
        if (auto *IDom = DT->getNode(&B)->getIDom()) {
            ImmediateDomMap[&B] = IDom->getBlock();
        }
        if (isa<ReturnInst>(B.getTerminator())) {
            ReturnBlockVec.push_back(&B);
        }
    }
}

bool FunctionDomInformation::dominateReturn(Instruction &I) const {
    assert(I.getFunction() == F);
    auto *CurrBlock = I.getParent();
    bool AllDom = true;
    for (auto *Ret: ReturnBlockVec) {
        while (Ret != CurrBlock) {
            auto It = ImmediateDomMap.find(Ret);
            if (It == ImmediateDomMap.end()) {
                Ret = nullptr;
                break;
            }
            Ret = It->second;
        }
        if (!Ret) {
            AllDom = false;
            break;
        } else {
            assert(Ret == CurrBlock);
        }
    }
    return AllDom;
}

