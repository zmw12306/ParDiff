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

#ifndef MEMORY_GLOBALMEMORYBLOCK_H
#define MEMORY_GLOBALMEMORYBLOCK_H

#include "Memory/MemoryBlock.h"

class GlobalMemoryBlock : public MemoryBlock {
private:
    enum GMKind {
        GMK_ConstantDataArray,
        GMK_Unknown
    };

    GMKind Kind;

public:
    GlobalMemoryBlock(Type *Ty, unsigned Num = 1) : MemoryBlock(Ty, Num, MK_Global), Kind(GMK_Unknown) {}

    bool isConstantDataArray() { return Kind == GMK_ConstantDataArray; }

    void setConstantDataArray() { Kind = GMK_ConstantDataArray; }

public:
    static bool classof(const MemoryBlock *M) {
        return M->getKind() == MK_Global;
    }
};

#endif //MEMORY_GLOBALMEMORYBLOCK_H
