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

#ifndef CORE_EXECUTOR_H
#define CORE_EXECUTOR_H

#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Value.h>
#include <llvm/Support/Debug.h>

#include "Core/DistinctMetadataAnalysis.h"
#include "Core/DomInformationAnalysis.h"
#include "Core/ExecutionState.h"
#include "Core/LoopSummaryAnalysis.h"
#include "Core/LoopInformationAnalysis.h"
#include "Core/SliceGraph.h"
#include "Support/InstructionVisitor.h"

using namespace llvm;
class Executor : public InstructionVisitor<Executor> {
private:
    /// llvm pass that drives this executor
    Pass *DriverPass;

    /// the execution state before entering to a basic block
    /// a block may have multiple incoming edges, thus multiple incoming states
    std::map<BasicBlock *, std::vector<ExecutionState *>> StateMap;

    /// block -> { incoming block index -> condition }
    std::map<BasicBlock *, std::vector<z3::expr>> MergeCondMap;

    /// current state
    /// @{
    z3::expr PC;
    ExecutionState *ES = nullptr;
    std::set<AbstractValue *> EscapedMemoryRevision;
    /// @}

    /// loop info
    /// @{
    FunctionLoopInformation *FLI = nullptr;
    std::vector<LoopSummaryAnalysis *> LoopStack;
    /// @}

    /// control the order of blocks to analyze
    /// @{
    unsigned LastProcessingBlockPointer = 0;
    unsigned ProcessingBlockPointer = 0;
    std::map<SingleLoop *, unsigned> LoopHeaderIdxMap;
    /// @}

    /// count the number of merging during the analysis
    static unsigned MergeID;
    static unsigned LoopAnalysisID;

    /// collect source code level type info
    DistinctMetadataAnalysis *DMA = nullptr;
    static std::map<Value *, DIType *> ValueDebugTypeMap;

public:
    explicit Executor(Pass *P) : DriverPass(P), PC(Z3::bool_val(true)) {}

    ~Executor() = default;

    z3::expr getPC() const { return PC; };

public:
#define HANDLE_INST(NUM, OPCODE, CLASS) \
    void visit##OPCODE(CLASS &I);

#include "llvm/IR/Instruction.def"

    void beforeVisit(Instruction &I);

    void afterVisit(Instruction &I);

    void beforeVisit(BasicBlock &B);

    void afterVisit(BasicBlock &B);

    void visitFunction(Function &F);

private:
    /// @{
    void trunc(Value *DstVal, Value *SrcVal);

    void zext(Value *DstVal, Value *SrcVal);

    void sext(Value *DstVal, Value *SrcVal);
    /// @}

    /// @{
    void visitpardiffMakeMessage(CallInst &I);

    void visitpardiffMakeMessageLen(CallInst &I);

    void visitpardiffMakeNamedObject(CallInst &I);

    void visitMemCpy(CallInst &I);

    void visitMemMov(CallInst &I);

    void visitMemSet(CallInst &I);

    void visitMemCmp(CallInst &I);

    void visitByteSwap(CallInst &I);

    void visitIsConstant(CallInst &I);

    void visitMalloc(CallInst &I);

    void visitCalloc(CallInst &I);

    void visitSSQBufStrLen(CallInst &I);

    void visitStrNCmp(CallInst &I);

    void visitStrCmp(CallInst &I);

    void visitCallIPA(CallInst &I);

    void visitCallDefault(CallInst &I);

    void visitDbgValue(DbgValueInst &I);

    void visitDbgDeclare(DbgDeclareInst &I);
    /// @}

    void alloc(MemoryBlock::MemoryKind MemTy, Instruction *Ret, Type *AllocTy, unsigned Num);

    void propagate(BasicBlock *From, BasicBlock *To, ExecutionState *State);

    void load(LoadInst *, AddressValue *, AbstractValue *);

    void _load(LoadInst *, AbstractValue *Dst, MemoryBlock *Addr, const z3::expr &Off);

    void store(StoreInst *, AddressValue *, AbstractValue *);

    void _store(StoreInst *, AbstractValue *V2S, MemoryBlock *Mem, const z3::expr &Off, const z3::expr &Cond, bool SU);

    void memoryCopy(Instruction *I, AddressValue *Dst, AddressValue *Src, AbstractValue *Len);

    void memoryCopy(Instruction *I, AddressValue *Dst, AddressValue *Src, uint64_t Len);

    void memoryCopy(Instruction *I, AddressValue *Dst, AddressValue *Src, const z3::expr &Len);

    void sortBlocks(Function &F, std::vector<BasicBlock *> &DFSOrderVec);

    bool compareLength(ICmpInst *I);

    void packing(ReturnInst &I);

    bool packable(ReturnInst &, z3::expr_vector);

    void initializeGlobals(Function &F);

    void naming(Function *F, Value *Val, DIVariable *DIV);

    bool hasPhi(BasicBlock *) const;

    GlobalMemoryBlock *isConstantString(Value *PtrVal);

    void recordMemoryWritten(Instruction *I, MemoryBlock *Mem, AbstractValue *Key);

    void recordMemoryRead(Instruction *I, MemoryBlock *Mem, AbstractValue *Key);

    /// infer DIType
    /// @{
    void inferDITypePHI(PHINode &);

    void inferDITypeBitCast(BitCastInst &);

    void inferDITypeSelect(SelectInst &);

    void inferDITypeLoad(LoadInst &);

    void inferDITypeGEP(GetElementPtrInst &);

    std::string getStructFieldName(Value *);

    std::string getVariableName(Instruction *);

    bool getBytes2Name(const z3::expr &Expr, z3::expr_vector &Vec);
    /// @}
};

#endif //CORE_EXECUTOR_H
