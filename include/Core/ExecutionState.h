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

#ifndef CORE_EXECUTIONSTATE_H
#define CORE_EXECUTIONSTATE_H

#include <llvm/IR/BasicBlock.h>

#include <map>
#include <set>

#include "Memory/GlobalMemoryBlock.h"
#include "Memory/HeapMemoryBlock.h"
#include "Memory/MessageBuffer.h"
#include "Memory/StackMemoryBlock.h"

using namespace llvm;

class ExecutionState {
private:
#ifndef NDEBUG
    /// where the state is forked from
    /// @{
    BasicBlock *ForkBlock = nullptr;
    unsigned ForkBlockBr = 0;
    /// @}
#endif

    /// record the path conditions that only relates to message buffer
    std::vector<z3::expr> PC;

    /// values really used in this state
    std::map<AbstractValue *, std::shared_ptr<AbstractValue>> AbsValRevisionMap;

    /// named message bytes, use the expr id for efficiency
    std::set<unsigned> NamedByteSet;

public:
    ExecutionState();

    ~ExecutionState();

public:
    /// fork for the I-th branch of the basic block B
    ExecutionState *fork(BasicBlock *B, unsigned I, bool LoopExiting = false);

    /// fork by copy
    ExecutionState *fork();

    /// merge the state ES to the current state
    void merge(BasicBlock *B, unsigned MergeID, std::vector<ExecutionState *> &ES, std::vector<z3::expr> &MergeCond);

public:
    /// memory allocation and deallocation
    /// @{
    MemoryBlock *stackAllocate(Function *F, Type *Ty, unsigned Num = 1);

    MemoryBlock *heapAllocate(Type *Ty, unsigned Num = 1);

    MemoryBlock *globalAllocate(Type *Ty, unsigned Num = 1);

    MemoryBlock *messageAllocate(Type *Ty, unsigned Num = 1);

    AbstractValue *registerAllocate(Value *V);

    void registerDeallocate(Value *V);
    /// @}

    /// operations on registers
    /// @{
    AbstractValue *bindValue(Value *V, Value *OldV);

    AbstractValue *boundValue(Value *V);
    /// @}

    /// @{
    /// get path condition over the message buffer as a whole
    z3::expr pc() const;

    /// get path condition at an index < pcLength()
    z3::expr pc(unsigned I) const;

    /// get path condition from index
    z3::expr pc(unsigned I, unsigned N) const;

    /// return the length of the current pc
    unsigned pcLength() const { return PC.size(); }

    /// add an extra condition to current pc
    void addPC(const z3::expr &);

    /// replace the conditions from a specified index with a given condition
    void replacePC(unsigned, const z3::expr &);
    /// @}

    /// get the exact abstract value used in this state, either for store or not
    AbstractValue *getValue(AbstractValue *Val, bool Store);

    /// after returning from the function \p F
    /// try to release useless memory allocated in message buffer, register, and stack
    void gc(Function *F);

    /// call the function before a function call
    void markCall();

    /// given a byte id, check if it is named or not
    bool named(unsigned ID) { return NamedByteSet.count(ID); }

    /// get the branch condition
    z3::expr condition(BasicBlock *B, unsigned I);

private:
    void merge(unsigned MergeID,
               const std::map<AbstractValue *, std::vector<std::pair<AbstractValue*, unsigned>>> &,
               const std::vector<z3::expr> &);

    AbstractValue *createAbstractValue4Constant(Constant *);

    bool conflict(const z3::expr &);

    friend raw_ostream &operator<<(llvm::raw_ostream &, ExecutionState &);

    bool optimize(std::vector<std::pair<AddressValue *, z3::expr>> &);

    std::shared_ptr<AddressValue> optimize2(std::vector<std::pair<AddressValue *, z3::expr>> &, unsigned PhiID);
};

raw_ostream &operator<<(llvm::raw_ostream &, ExecutionState &);

#endif //CORE_EXECUTIONSTATE_H
