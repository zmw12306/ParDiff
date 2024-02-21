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

#include <llvm/Support/CommandLine.h>
#include <llvm/Support/Debug.h>
#include <llvm/Support/Format.h>
#include "Core/LoopInformationAnalysis.h"

#define DEBUG_TYPE "LoopInformationAnalysis"

using namespace llvm;

char LoopInformationAnalysis::ID = 0;
static RegisterPass<LoopInformationAnalysis> X(DEBUG_TYPE, "A module pass of loop info");

LoopInformationAnalysis::~LoopInformationAnalysis() {
    for (auto &It: LoopInfoMap) {
        delete It.second;
    }
}

void LoopInformationAnalysis::getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesAll();
    AU.addRequired<LoopInfoWrapperPass>();
}

bool LoopInformationAnalysis::runOnModule(Module &M) {
    return false;
}

FunctionLoopInformation *LoopInformationAnalysis::getLoopInfo(Function &F) {
    if (F.empty()) return nullptr;
    auto *LI = &getAnalysis<LoopInfoWrapperPass>(F).getLoopInfo();
    auto *FLI = new FunctionLoopInformation(LI);
    LoopInfoMap[&F] = FLI;
    return FLI;
}

FunctionLoopInformation::FunctionLoopInformation(LoopInfo *LI) {
    auto AllLoops = LI->getLoopsInPreorder();
    for (auto *Loop: AllLoops) {
        auto Wrapper = std::make_shared<SingleLoop>(Loop);
        HeaderLoopMap[Loop->getHeader()] = Wrapper;
        LatchLoopMap[Loop->getLoopLatch()] = Wrapper;

        SmallVector<BasicBlock *, 4> Blocks;
        Loop->getExitingBlocks(Blocks);
        for (auto *Exiting: Blocks)
            ExitingLoopMap[Exiting] = Wrapper;
    }
}

SingleLoop::SingleLoop(Loop *LP) {
    for (auto *B: LP->getBlocks()) Blocks.insert(B);
    SmallVector<BasicBlock *, 8> Succs;
    LP->getExitBlocks(Succs);
    for (auto *B: Succs) ExitBlocks.push_back(B);
    Succs.clear();
    LP->getExitingBlocks(Succs);
    for (auto *B: Succs) ExitingBlocks.insert(B);
    Header = LP->getHeader();
    Latch = LP->getLoopLatch();
    assert(Latch->getTerminator()->getNumSuccessors() == 1);
}
