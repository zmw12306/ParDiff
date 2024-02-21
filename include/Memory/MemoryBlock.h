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

#ifndef MEMORY_MEMORYBLOCK_H
#define MEMORY_MEMORYBLOCK_H

#include <llvm/IR/DataLayout.h>
#include <llvm/Support/Casting.h>
#include <cstdio>
#include <vector>
#include "Memory/AbstractValue.h"

class MemoryBlock {
public:
    enum MemoryKind {
        MK_Stack,
        MK_Heap,
        MK_Global,
        MK_Message,
    };

protected:
    MemoryKind Kind;
    std::vector<AbstractValue *> Mem;
    std::map<unsigned, unsigned> OffsetIDMap;

public:
    MemoryBlock(Type *Ty, unsigned Num, MemoryKind K);

    virtual ~MemoryBlock();

    virtual AbstractValue *at(size_t Offset);

    virtual AbstractValue *at(const z3::expr &Offset);

    [[nodiscard]] size_t size() const;

    [[nodiscard]] MemoryKind getKind() const { return Kind; }

    [[nodiscard]] std::vector<AbstractValue *>::iterator begin() { return Mem.begin(); }

    [[nodiscard]] std::vector<AbstractValue *>::iterator end() { return Mem.end(); }

private:
    void allocate(Type *Ty, unsigned Num);

    void allocate(Type *Ty);
};

#endif //MEMORY_MEMORYBLOCK_H
