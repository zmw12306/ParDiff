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

#ifndef TRANSFORM_AUTOFORMATPASS_H
#define TRANSFORM_AUTOFORMATPASS_H

#include <llvm/IR/Module.h>
#include <llvm/Pass.h>

using namespace llvm;

/// NDSS'08 Automatic Protocol Format Reverse Engineering through Context-Aware Monitored Execution
class AutoFormatPass : public ModulePass {
private:
    const DataLayout *DL;

public:
    static char ID;

    AutoFormatPass() : ModulePass(ID), DL(0) {}

    ~AutoFormatPass() override = default;

    void getAnalysisUsage(AnalysisUsage &) const override;

    bool runOnModule(Module &) override;

private:
    void instrument(Function &);
};

#endif //TRANSFORM_AUTOFORMATPASS_H
