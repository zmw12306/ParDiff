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

#ifndef pardiff_LIFTINGPROTOCOLFORMATPASS_H
#define pardiff_LIFTINGPROTOCOLFORMATPASS_H

#include <llvm/IR/Module.h>
#include <llvm/Pass.h>

using namespace llvm;

class LiftingProtocolFormatPass : public ModulePass {
public:
    static char ID;

    LiftingProtocolFormatPass() : ModulePass(ID) {}

    ~LiftingProtocolFormatPass() override = default;

    void getAnalysisUsage(AnalysisUsage &) const override;

    bool runOnModule(Module &) override;

private:
    void checkBuiltInFunctions(Module &M);
};

#endif /* pardiff_LIFTINGPROTOCOLFORMATPASS_H */
