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
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/Debug.h>
#include <llvm/Support/Format.h>

#include "BNF/BNF.h"
#include "Core/DistinctMetadataAnalysis.h"
#include "Core/DomInformationAnalysis.h"
#include "Core/Executor.h"
#include "Core/LoopInformationAnalysis.h"
#include "Core/PLang.h"
#include "Core/SliceGraph.h"
#include "Core/SymbolicExecution.h"
#include "Core/SymbolicExecutionTree.h"
#include "LiftingProtocolFormatPass.h"
#include "Support/Debug.h"
#include "Support/DL.h"
#include "Support/TimeRecorder.h"
#include "Support/Z3.h"

#define DEBUG_TYPE "LiftingProtocolFormatPass"

using namespace llvm;

static cl::opt<std::string> EntryFunctionName("pardiff-entry",
                                              cl::desc("specify from which function we start our analysis"),
                                              cl::init("pardiff_main"));
static cl::opt<std::string> Dot("pardiff-dot",
                                cl::desc("output intermediate graphic code representation"),
                                cl::init(""));
static cl::opt<std::string> EnablePLang("pardiff-enable-p",
                                        cl::desc("output code in P"),
                                        cl::init(""));
static cl::opt<bool> EnableBNF("pardiff-text-bnf",
                               cl::desc("output text bnf"),
                               cl::init(true));

char LiftingProtocolFormatPass::ID = 0;
static RegisterPass<LiftingProtocolFormatPass> X(DEBUG_TYPE, "The core engine of pardiff.");

void LiftingProtocolFormatPass::getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesAll();
    AU.addRequired<LoopInformationAnalysis>();
    AU.addRequired<DomInformationAnalysis>();
    AU.addRequired<DistinctMetadataAnalysis>();
}

bool LiftingProtocolFormatPass::runOnModule(Module &M) {
    DL::initialize(M.getDataLayout());
    Z3::initialize();
    checkBuiltInFunctions(M);

    auto *Entry = M.getFunction(EntryFunctionName.getValue());
    if (!Entry) {
        std::string ErrorMsg("The entry function --- ");
        ErrorMsg.append(EntryFunctionName.getValue());
        ErrorMsg.append(" --- is not found!");
        pardiff_WARN(ErrorMsg.c_str());

        bool MultipleEntries = false;
        for (auto &F: M) {
            if (!F.isDeclaration() && F.getName().startswith("pardiff_main_")) {
                if (Entry) MultipleEntries = true;
                if (!Entry) Entry = &F;
                pardiff_WARN("\tPossible entry --- " + F.getName().str());
            }
        }
        //exit(1);
        if (MultipleEntries) exit(1);
    }

    TimeRecorder Timer("Lifting the protocol");
    auto PC = Z3::bool_val(true);
    {
        TimeRecorder AITimer("Step 1: Abstract interpreting the code");
        Executor Exe(this);
        Exe.visit(Entry);
        PC = Exe.getPC();
    }

    {
        TimeRecorder SETimer("Step 2: Executing on the slice");
        SliceGraph *Slice = SliceGraph::get(PC);
        assert(Slice);
        if (!Dot.getValue().empty()) Slice->dot(Dot.getValue(), "graph");
        Slice->simplifyBeforeSymbolicExecution();
        if (!Dot.getValue().empty()) Slice->dot(Dot.getValue(), "graph.simplify");
        SymbolicExecutionTree *Tree = SymbolicExecution().run(PC, *Slice);
        delete Slice;
        Tree->simplify();
        if (!Dot.getValue().empty()) Tree->dot(Dot.getValue(), "tree");
        PC = Tree->pc();
        delete Tree;
    }

    {
        TimeRecorder BNFTimer("Step 3: Generating BNF");
        auto PhiVec = Z3::find_all(PC, true, [](const z3::expr &E) { return Z3::is_phi(E); });
        assert(PhiVec.empty());
        auto *NewSlice = SliceGraph::get(PC, true);
        NewSlice->simplifyAfterSymbolicExecution();

        if (!Dot.getValue().empty()) NewSlice->dot(Dot.getValue(), "bnf");
        
        //correct here
        if (EnableBNF.getValue()){
           
            //errs()<<"***   print out the PC: \n";
            //errs() << NewSlice->pc() <<"\n";//bnf->pc, unsorted
            // BNFRef B = BNF::get(NewSlice->pc());
            // outs() <<"outs BNF: "<< B << "\n";   

            // errs()<<"----print out the size of productions: "<<B->Products.size()<<"\n";
            // SliceGraph *Slice = getGraph(B);
            
            graphsForDiff.insert(graphsForDiff.end(),NewSlice->pc());
            //errs()<<"***   insert success: \n";
            // if (!Dot.getValue().empty()) 
            //     Slice->dot(Dot.getValue(), "SortedGraph");
                  
        }
             
        if (EnablePLang.getNumOccurrences()) PLang(NewSlice).dump(EnablePLang.getValue());
        delete NewSlice;
    }
    return false;
}

void LiftingProtocolFormatPass::checkBuiltInFunctions(Module &M) {
    /*
     * void *pardiff_make_object(uint64_t size);
     * void *pardiff_make_named_object(uint64_t size, const char *);
     * void pardiff_make_global(void *);
     * void *pardiff_make_message(void);
     * uint16_t pardiff_make_message_length(void);
     */

    auto *pardiffMakeObject = M.getFunction("pardiff_make_object");
    if (pardiffMakeObject) {
        assert(pardiffMakeObject->getReturnType()->isPointerTy());
        assert(pardiffMakeObject->arg_size() == 1);
        assert(pardiffMakeObject->getArg(0)->getType()->isIntegerTy());
    }

    auto *pardiffMakeNamedObject = M.getFunction("pardiff_make_named_object");
    if (pardiffMakeNamedObject) {
        assert(pardiffMakeNamedObject->getReturnType()->isPointerTy());
        assert(pardiffMakeNamedObject->arg_size() == 2);
        assert(pardiffMakeNamedObject->getArg(0)->getType()->isIntegerTy());
        assert(pardiffMakeNamedObject->getArg(1)->getType()->isPointerTy());
    }

    auto *pardiffMakeMessage = M.getFunction("pardiff_make_message");
    if (pardiffMakeMessage) {
        assert(pardiffMakeMessage->getReturnType()->isPointerTy());
        assert(pardiffMakeMessage->arg_size() == 0);
    }

    auto *pardiffMakeMessageLength = M.getFunction("pardiff_make_message_length");
    if (pardiffMakeMessageLength) {
        assert(pardiffMakeMessageLength->getReturnType()->isIntegerTy());
        assert(pardiffMakeMessageLength->arg_size() == 0);
    }
}
