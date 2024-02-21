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

#ifndef CORE_DOMINFORMATIONANALYSIS_H
#define CORE_DOMINFORMATIONANALYSIS_H

#include <llvm/IR/Dominators.h>
#include <llvm/IR/Module.h>
#include <llvm/Pass.h>
#include <set>

using namespace llvm;

class FunctionDomInformation {
private:
    /// the current function
    Function *F;

    /// the value is the idom of the key
    std::map<BasicBlock *, BasicBlock *> ImmediateDomMap;

    /// return blocks
    std::vector<BasicBlock *> ReturnBlockVec;

public:
    FunctionDomInformation(Function *, DominatorTree *);

    bool dominateReturn(Instruction &I) const;
};

class DomInformationAnalysis : public ModulePass {
private:
    std::map<Function *, FunctionDomInformation *> DomInfoMap;

public:
    static char ID;

    DomInformationAnalysis() : ModulePass(ID) {}

    ~DomInformationAnalysis() override;

    void getAnalysisUsage(AnalysisUsage &) const override;

    bool runOnModule(Module &) override;

    FunctionDomInformation *getDomInfo(Function &);
};

#endif //CORE_DOMINFORMATIONANALYSIS_H
