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

#include <llvm/Support/ErrorHandling.h>
#include "Memory/MemoryBlock.h"

MemoryBlock::MemoryBlock(Type *Ty, unsigned Num, MemoryKind K) : Kind(K) {
    allocate(Ty, Num);
}

MemoryBlock::~MemoryBlock() {
    for (auto *AV: Mem) delete AV;
}

void MemoryBlock::allocate(Type *Ty, unsigned Num) {
    assert(Ty && "Error: allocate memory without type!");
    assert(Num && "Error: allocate memory with size zero!");

    std::vector<Type *> TypeVec;
    DL::flatten(Ty, TypeVec, true);
    unsigned CurrOffset = 0;
    for (unsigned J = 0; J < Num; ++J) {
        for (unsigned K = 0; K < TypeVec.size(); ++K) {
            allocate(TypeVec[K]);
            OffsetIDMap[CurrOffset] = Mem.size() - 1;
            CurrOffset = CurrOffset + Mem.back()->bytewidth();
        }
    }
    OffsetIDMap[CurrOffset] = Mem.size();
}

void MemoryBlock::allocate(Type *Ty) {
    if (Ty->isPointerTy()) {
        auto *AV = new AddressValue();
        Mem.push_back(AV);
    } else {
        auto *AV = new ScalarValue(DL::getNumBytes(Ty));
        Mem.push_back(AV);
    }
}

AbstractValue *MemoryBlock::at(size_t Offset) {
    if (Offset == 0)
        return Mem.empty() ? nullptr : Mem[0];

    auto It = OffsetIDMap.find(Offset);
    assert(It != OffsetIDMap.end());
    auto ID = It->second;
    assert(ID <= Mem.size());
    if (ID == Mem.size())
        return nullptr;
    return Mem[ID];
}

AbstractValue *MemoryBlock::at(const z3::expr &Offset) {
    uint64_t Off;
    if (Z3::is_numeral_u64(Offset, Off)) {
        return at(Off);
    }
    errs() << "offset : " << Offset << "\n";
    errs() << "kind : " << this->getKind() << "\n";
    llvm_unreachable("Error: symbolic offset in a non-mb memory space");
}

size_t MemoryBlock::size() const {
    return Mem.size();
}
