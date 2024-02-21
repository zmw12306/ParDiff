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
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/Debug.h>
#include "AutoFormatPass.h"

#define DEBUG_TYPE "AutoFormatPass"

char AutoFormatPass::ID = 0;
static RegisterPass<AutoFormatPass> X(DEBUG_TYPE, "instrument a program for autoformat");

static cl::opt<int> BufferArg(
        "af-buffer",
        cl::desc("allows we set break point at some place"),
        cl::init(-1));

static cl::opt<int> LenArg(
        "af-len",
        cl::desc("allows we set break point at some place"),
        cl::init(-1));

static cl::opt<std::string> ParsingFunc(
        "af-parser",
        cl::desc("allows we set break point at some place"),
        cl::init(""));

/// these functions should be implemented as a third-party lib and linked to the instrumented code
/// @{
/// static void *buf_base = 0;
/// static unsigned buf_len = 0;
/// static bool start_logging = 0;
/// void autoformat_beginning(void* base, uint64_t buf_len) {
///     buf_base = base; buf_len = len;
///     start_logging = 1;
/// }
static const char *BeginningFunction = "autoformat_beginning";
static Function *BeginningFunc = nullptr;

/// these functions should be implemented as a third-party lib and linked to the instrumented code
/// @{
/// static void *buf_base = 0;
/// static unsigned buf_len = 0;
/// static bool start_logging = 0;
/// void autoformat_end() {
///     buf_base = 0; buf_len = 0;
///     start_logging = 0;
/// }
static const char *EndFunction = "autoformat_end";
static Function *EndFunc = nullptr;

/// void autoformat_logging(void* ptr, uint64_t nbytes) {
///    for (unsigned x = 0; x < nbytes; ++x)
///     if (start_logging && ptr + x - buf_base >= 0 && ptr + x - buf_base < buf_len) {
///          // logging the offset and the global call stack
///      }
/// }
static const char *LoggingFunction = "autoformat_logging";
static Function *LoggingFunc = nullptr;

/// uint64_t *call_stack = 0;
/// uint64_t call_stack_len = 0;
/// uint64_t call_stack_ptr = 0;
/// void autoformat_pushing(uint64_t func_id) {
///    if (!start_logging) return;
///    if (call_stack == 0) {
///         call_stack = malloc(1000); call_stack_len = 1000;
///     } else if (call_stack_ptr >= call_stack_len) {
///         call_stack = realloc(call_stack_len + 500); call_stack_len += 500;
///     }
///     call_stack[call_stack_ptr++] = func_id;
/// }
static const char *PushingFunction = "autoformat_pushing";
static Function *PushingFunc = nullptr;

/// void autoformat_popping() {
///      if (!start_logging) return;
///      assert(call_stack_ptr > 0);
///      call_stack_ptr--;
///      if (call_stack_ptr == 0) start_logging = 0; // this means we exit the entry func
/// }
static const char *PoppingFunction = "autoformat_popping";
static Function *PoppingFunc = nullptr;
/// @}

void AutoFormatPass::getAnalysisUsage(AnalysisUsage &AU) const {
}

bool AutoFormatPass::runOnModule(Module &M) {
    DL = &M.getDataLayout();

    auto *BeginningFuncTy = FunctionType::get(Type::getVoidTy(M.getContext()),
                                              {Type::getInt8PtrTy(M.getContext()), Type::getInt64Ty(M.getContext())},
                                              false);
    BeginningFunc = (Function *) M.getOrInsertFunction(BeginningFunction, BeginningFuncTy).getCallee();

    auto *EndFuncTy = FunctionType::get(Type::getVoidTy(M.getContext()),
                                        {},
                                        false);
    EndFunc = (Function *) M.getOrInsertFunction(EndFunction, EndFuncTy).getCallee();

    auto *LoggingFuncTy = FunctionType::get(Type::getVoidTy(M.getContext()),
                                            {Type::getInt8PtrTy(M.getContext()), Type::getInt64Ty(M.getContext())},
                                            false);
    LoggingFunc = (Function *) M.getOrInsertFunction(LoggingFunction, LoggingFuncTy).getCallee();

    auto *PushingFuncTy = FunctionType::get(Type::getVoidTy(M.getContext()),
                                            {Type::getInt64Ty(M.getContext())},
                                            false);
    PushingFunc = (Function *) M.getOrInsertFunction(PushingFunction, PushingFuncTy).getCallee();

    auto *PoppingFuncTy = FunctionType::get(Type::getVoidTy(M.getContext()),
                                            {},
                                            false);
    PoppingFunc = (Function *) M.getOrInsertFunction(PoppingFunction, PoppingFuncTy).getCallee();

    for (auto &F: M) {
        if (F.isDeclaration()) continue;
        instrument(F);
        if (verifyFunction(F, &errs())) {
            errs() << F << "\n";
            llvm_unreachable("Failed to verify");
        }
    }
    return false;
}

void AutoFormatPass::instrument(Function &F) {
    outs() << "[autoformat] Transforming " << F.getName() << "\n";
    // step 1: instrument for call stack
    auto *EntryBlock = &F.getEntryBlock();
    std::vector<Instruction *> CallInstructions;
    for (auto &B: F) {
        for (auto &I: B) {
            if (isa<CallInst>(I)) {
                CallInstructions.push_back(&I);
            }
        }
    }
    for (auto *Call: CallInstructions) {
        CallInst::Create(PushingFunc->getFunctionType(), PushingFunc,
                         {ConstantInt::getSigned(Type::getInt64Ty(F.getContext()), (int64_t) Call)},
                         "", Call);
        auto *Next = Call->getNextNode();
        CallInst::Create(PoppingFunc->getFunctionType(), PoppingFunc, {}, "", Next);
    }

    // step 2: instrument the entry function
    if (F.getName() == ParsingFunc.getValue()) {
        // insert start function
        int BufArgId = BufferArg.getValue();
        int LenArgId = LenArg.getValue();
        assert(BufArgId >= 0 && LenArgId >= 0);
        auto *FirstInsertPt = &*EntryBlock->getFirstInsertionPt();
        auto *BufferPtr = CastInst::CreateBitOrPointerCast(F.getArg(BufArgId), Type::getInt8PtrTy(F.getContext()),
                                                           "",
                                                           FirstInsertPt);
        auto *BufferLen = CastInst::CreateZExtOrBitCast(F.getArg(LenArgId), Type::getInt64Ty(F.getContext()),
                                                        "",
                                                        FirstInsertPt);
        CallInst::Create(BeginningFunc->getFunctionType(), BeginningFunc,
                         {BufferPtr, BufferLen},
                         "", FirstInsertPt);

        // insert end function
        std::vector<Instruction *> ReturnInstructions;
        for (auto &B: F) {
            for (auto &I: B) {
                if (isa<ReturnInst>(I)) {
                    ReturnInstructions.push_back(&I);
                }
            }
        }
        for (auto *Ret: ReturnInstructions) {
            CallInst::Create(EndFunc->getFunctionType(), EndFunc, {}, "", Ret);
        }
    }

    // step 3: instrument for load/memcpy inst
    std::vector<Instruction *> LoadInstructions;
    std::vector<CallInst *> MCpyInstructions;
    for (auto &B: F) {
        for (auto &I: B) {
            if (isa<LoadInst>(I)) {
                LoadInstructions.push_back(&I);
            } else if (auto *Call = dyn_cast<CallInst>(&I)) {
                if (Call->getCalledFunction()) {
                    switch (Call->getCalledFunction()->getIntrinsicID()) {
                        case Intrinsic::memcpy_element_unordered_atomic:
                        case Intrinsic::memcpy:
                            MCpyInstructions.push_back(Call);
                            break;
                    }
                }
            }
        }
    }
    for (auto *Ld: LoadInstructions) {
        auto *LoadTy = Ld->getType();
        if (!LoadTy->isIntegerTy()) continue;

        auto Ptr = CastInst::CreateBitOrPointerCast(Ld->getOperand(0), Type::getInt8PtrTy(F.getContext()),
                                                    "",
                                                    Ld);
        CallInst::Create(LoggingFunc->getFunctionType(), LoggingFunc,
                         {Ptr, ConstantInt::getSigned(Type::getInt64Ty(F.getContext()),
                                                      DL->getTypeStoreSize(LoadTy))},
                         "", Ld);
    }

    for (auto *MCpy: MCpyInstructions) {
        auto *Ptr = MCpy->getArgOperand(1);
        assert(Ptr->getType()->isPointerTy());
        assert(Ptr->getType()->getPointerElementType()->isIntegerTy());
        if (!Ptr->getType()->getPointerElementType()->isIntegerTy(8)) {
            Ptr = CastInst::CreateBitOrPointerCast(Ptr, Type::getInt8PtrTy(F.getContext()), "", MCpy);
        }

        auto *Size = MCpy->getArgOperand(2);
        assert(Size->getType()->isIntegerTy());
        if (!Size->getType()->isIntegerTy(64)) {
            Size = CastInst::CreateZExtOrBitCast(Size, Type::getInt64Ty(F.getContext()), "", MCpy);
        }

        CallInst::Create(LoggingFunc->getFunctionType(), LoggingFunc, {Ptr, Size}, "", MCpy);
    }
}