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

#ifndef CORE_LOOPINFORMATIONANALYSIS_H
#define CORE_LOOPINFORMATIONANALYSIS_H

#include <llvm/Analysis/LoopInfo.h>
#include <llvm/IR/Module.h>
#include <llvm/Pass.h>
#include <set>

using namespace llvm;

class SingleLoop {
private:
    BasicBlock *Header;
    BasicBlock *Latch;
    std::set<BasicBlock *> Blocks;
    std::set<BasicBlock *> ExitingBlocks;
    std::vector<BasicBlock *> ExitBlocks;

public:
    explicit SingleLoop(Loop *);

    bool contains(BasicBlock *B) const { return Blocks.count(B); }

    bool containsExit(BasicBlock *B) const { return std::count(ExitBlocks.begin(), ExitBlocks.end(), B); }

    bool containsExiting(BasicBlock *B) const { return ExitingBlocks.count(B); }

    BasicBlock *getHeader() const { return Header; }

    BasicBlock *getLatch() const { return Latch; }

    std::set<BasicBlock *>::const_iterator begin() const { return Blocks.begin(); }

    std::set<BasicBlock *>::const_iterator end() const { return Blocks.end(); }

    std::set<BasicBlock *>::const_iterator exiting_begin() const { return ExitingBlocks.begin(); }

    std::set<BasicBlock *>::const_iterator exiting_end() const { return ExitingBlocks.end(); }

    std::vector<BasicBlock *>::const_iterator exit_begin() const { return ExitBlocks.begin(); }

    std::vector<BasicBlock *>::const_iterator exit_end() const { return ExitBlocks.end(); }
};

class FunctionLoopInformation {
private:
    std::map<BasicBlock *, std::shared_ptr<SingleLoop>> HeaderLoopMap;
    std::map<BasicBlock *, std::shared_ptr<SingleLoop>> LatchLoopMap;
    std::map<BasicBlock *, std::shared_ptr<SingleLoop>> ExitingLoopMap;

public:
    explicit FunctionLoopInformation(LoopInfo *);

    SingleLoop *isLoopHeader(BasicBlock *B) {
        auto It = HeaderLoopMap.find(B);
        return It == HeaderLoopMap.end() ? nullptr : It->second.get();
    }

    SingleLoop *isLoopLatch(BasicBlock *B) {
        auto It = LatchLoopMap.find(B);
        return It == LatchLoopMap.end() ? nullptr : It->second.get();
    }

    SingleLoop *isLoopExiting(BasicBlock *B) {
        auto It = ExitingLoopMap.find(B);
        return It == ExitingLoopMap.end() ? nullptr : It->second.get();
    }
};

class LoopInformationAnalysis : public ModulePass {
private:
    std::map<Function *, FunctionLoopInformation *> LoopInfoMap;

public:
    static char ID;

    LoopInformationAnalysis() : ModulePass(ID) {}

    ~LoopInformationAnalysis() override;

    void getAnalysisUsage(AnalysisUsage &) const override;

    bool runOnModule(Module &) override;

    FunctionLoopInformation *getLoopInfo(Function &);
};

#endif //CORE_LOOPINFORMATIONANALYSIS_H
