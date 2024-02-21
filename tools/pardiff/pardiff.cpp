/*
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

#include <llvm/Analysis/CallGraph.h>
#include <llvm/Analysis/CallGraphSCCPass.h>
#include <llvm/Analysis/LoopPass.h>
#include <llvm/Analysis/TargetLibraryInfo.h>
#include <llvm/Analysis/TargetTransformInfo.h>
#include <llvm/Bitcode/BitcodeWriterPass.h>
#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/IRPrintingPasses.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/InitializePasses.h>
#include <llvm/LinkAllIR.h>
#include <llvm/Support/Debug.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/InitLLVM.h>
#include <llvm/Support/PluginLoader.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/Support/ToolOutputFile.h>
#include <llvm/Support/YAMLTraits.h>
#include <llvm/Transforms/Scalar.h>
#include <llvm/Transforms/Utils.h>
#include <llvm/Transforms/Utils/UnifyFunctionExitNodes.h>
#include "Support/TimeRecorder.h"
#include <memory>

#include "LiftingProtocolFormatPass.h"
#include "BNF/FSM.h"
#include "Support/Debug.h"
#include "Support/InstructionVisitor.h"
#include "BNF/BNF.h"
#include "Core/SliceGraph.h"
#include "Transform/LowerConstantExpr.h"
#include "Transform/LowerGlobalConstantArraySelect.h"
#include "Transform/LowerSelect.h"
#include "Transform/MergeReturn.h"
#include "Transform/NameBlock.h"
#include "Transform/RemoveDeadBlock.h"
#include "Transform/RemoveNoRetFunction.h"
#include "Transform/RemoveIrreducibleFunction.h"
#include "Transform/SimplifyLatch.h"

#include <vector>
#include <set>


using namespace llvm;


std::vector<z3::expr>graphsForDiff;
std::map<Product*, std::pair<std::string,std::string>> res_map1,res_map2;
std::map<Product*, BoundRef> To_map1, To_map2;


bool flag_for = false;


static cl::opt<std::string> InputFilename1(cl::Positional, cl::desc("<input bitcode file>"),
                                          cl::init("-"), cl::value_desc("filename"));

static cl::opt<std::string> InputFilename2(cl::Positional, cl::desc("<input bitcode file>"),
                                          cl::init("-"), cl::value_desc("filename"));

static cl::opt<std::string> OutputFilename("o", cl::desc("<output bitcode file>"),
                                           cl::init(""), cl::value_desc("filename"));

static cl::opt<bool> OutputAssembly("S", cl::desc("Write output as LLVM assembly"), cl::init(false));

static cl::opt<bool> OnlyTransform("t", cl::desc("Only do preprocessing transform without lifting the specifications"),
                                   cl::init(false));

class NotificationPass : public ModulePass {
private:
    const char *Message;

public:
    static char ID;

    explicit NotificationPass(const char *M) : ModulePass(ID), Message(M) {}

    ~NotificationPass() override = default;

    void getAnalysisUsage(AnalysisUsage &AU) const override {
        AU.setPreservesAll();
    }

    bool runOnModule(Module &) override {
        pardiff_INFO(Message);
        return false;
    }
};

char NotificationPass::ID = 0;

//global varaibles for the results of two versions


int main(int argc, char **argv) {
    InitLLVM X(argc, argv);

    // Enable debug stream buffering.
    llvm::EnableDebugBuffering = true;

    // Call llvm_shutdown() on exit.
    llvm_shutdown_obj Y;

    // Print a stack trace if a fatal signal occurs.
    sys::PrintStackTraceOnErrorSignal(argv[0]);
    PrettyStackTraceProgram Z(argc, argv);

    // Initialize passes
    PassRegistry &Registry = *PassRegistry::getPassRegistry();
    initializeCore(Registry);
    initializeCoroutines(Registry);
    initializeScalarOpts(Registry);
    initializeIPO(Registry);
    initializeAnalysis(Registry);
    initializeTransformUtils(Registry);
    initializeInstCombine(Registry);
    initializeAggressiveInstCombine(Registry);
    initializeTarget(Registry);

    cl::ParseCommandLineOptions(argc, argv, "Pardiff lifts protocol source code to protocol specifications\n");

    SMDiagnostic Err;
    LLVMContext Context;

    // the first graph
    std::unique_ptr<Module> M1 = parseIRFile(InputFilename1.getValue(), Err, Context);
    if (!M1) {
        Err.print(argv[0], errs());
        return 1;
    }

    if (verifyModule(*M1, &errs())) {
        errs() << argv[0] << ": error: input module is broken!\n";
        return 1;
    }

    // the second graph
    std::unique_ptr<Module> M2 = parseIRFile(InputFilename2.getValue(), Err, Context);
    if (!M2) {
        Err.print(argv[1], errs());
        return 1;
    }

    if (verifyModule(*M2, &errs())) {
        errs() << argv[1] << ": error: input module is broken!\n";
        return 1;
    }

    legacy::PassManager Passes;

    Passes.add(new NotificationPass("Start preprocessing the input bitcode ... "));
    Passes.add(createLowerAtomicPass());
    Passes.add(createLowerInvokePass());
    Passes.add(createPromoteMemoryToRegisterPass());
    Passes.add(createSCCPPass());
    Passes.add(createLoopSimplifyPass());
    Passes.add(new SimplifyLatch());
    Passes.add(new MergeReturn());
    Passes.add(new RemoveNoRetFunction());
    Passes.add(new RemoveIrreducibleFunction());
    Passes.add(new LowerConstantExpr());
    Passes.add(new LowerSelect());
    Passes.add(new RemoveDeadBlock());
    Passes.add(new LowerGlobalConstantArraySelect());
#ifndef NDEBUG
    Passes.add(new NameBlock());
#endif
    Passes.add(new NotificationPass("Start preprocessing the input bitcode ... ""Done!"));
    if (!OnlyTransform) Passes.add(new LiftingProtocolFormatPass());

    std::unique_ptr<ToolOutputFile> Out;
    if (!OutputFilename.getValue().empty()) {
        std::error_code EC;
        Out = std::make_unique<ToolOutputFile>(OutputFilename, EC, sys::fs::F_None);
        if (EC) {
            errs() << EC.message() << '\n';
            return 1;
        }

        if (OutputAssembly.getValue()) {
            Passes.add(createPrintModulePass(Out->os()));
        } else {
            Passes.add(createBitcodeWriterPass(Out->os()));
        }
    }

    Passes.add(new NotificationPass("Start preprocessing the diff of two programs "));
    Passes.add(new NotificationPass("Start to get BNF for the first implementation ... ""Done!"));
    Passes.run(*M1);
    errs()<<"\nInst num before slicing: "<<Inst.size()<<"\n";
    errs()<<"\nInst num after slicing: "<<slice_Inst.size()<<"\n";

    Passes.add(new NotificationPass("Start to get BNF for the second implementation ... ""Done!"));
    Passes.add(new NotificationPass("Start to get BNF for the first implementation ... ""Done!"));
    Inst.clear();
    slice_Inst.clear();
    Passes.run(*M2);
    errs()<<"\nInst num before slicing: "<<Inst.size()<<"\n";
    errs()<<"\nInst num after slicing: "<<slice_Inst.size()<<"\n";
    Passes.add(new NotificationPass("Start to get BNF for the second implementation ... ""Done!"));
    //errs()<<"***first:";
    //errs()<<graphsForDiff[0]<<"\n";
    //errs()<<"***second:";
    //errs()<<graphsForDiff[1]<<"\n";
    //errs()<<"save success in graphfordiff\n";
    Passes.add(new NotificationPass("Start to get-diff "));
    
    BNFRef BNF1 = BNF::get(graphsForDiff[0]);
    flag_for = true;
    BNFRef BNF2 = BNF::get(graphsForDiff[1]);
    errs()<<"\nBNF for the first version:\n"<<BNF1;
    errs()<<"\n\nBNF for the second version:\n"<<BNF2;
    FSMRef f1,f2;
    Passes.add(new NotificationPass("Start to generate FSM for two programs ... ""Done!"));
    
    {
        TimeRecorder FSM1Timer("Generate FSM1");
        errs()<<"start to construct the first FSM\n";
        f1 = FSM::getFSM(BNF1);
        errs()<<"Node num before simplify: "<<f1->allNodes.size()<<"\n";
        int edgenum =0;
        for(auto n: f1->allNodes){
            edgenum += n->transition.size();
        }
        errs()<<"Edge num before simplify: "<<edgenum<<"\n";
        f1->simplify();     
        errs()<<"\nFSM for the first version:\n"<<f1;
        errs()<<"Node num after simplify: "<<f1->allNodes.size()<<"\n";
        edgenum =0;
        for(auto n: f1->allNodes){
            edgenum += n->transition.size();
        }
        errs()<<"Edge num after simplify: "<<edgenum<<"\n";
    }
    {
        TimeRecorder FSM2Timer("Generate FSM2");
        errs()<<"start to construct the second FSM\n";
        f2 = FSM::getFSM(BNF2);
        errs()<<"Node num before simplify: "<<f2->allNodes.size()<<"\n";
        int edgenum2 =0;
        for(auto n: f2->allNodes){
            edgenum2 += n->transition.size();
        }
        errs()<<"Edge num before simplify: "<<edgenum2<<"\n";
        f2->simplify();
        errs()<<"\nFSM for the second version:\n"<<f2;
        errs()<<"Node num after simplify: "<<f2->allNodes.size()<<"\n";
        edgenum2 =0;
        for(auto n: f2->allNodes){
            edgenum2 += n->transition.size();
        }
        errs()<<"Edge num after simplify: "<<edgenum2<<"\n";
    }
    Passes.add(new NotificationPass("Start to get-diff ... ""Done!"));
    
    {
        TimeRecorder diffTimer("FSM diff");
        errs()<<"start to bisimulation\n";
        bisimulation(f1, f2);
    }

    if (Out) Out->keep();

    return 0;
}
