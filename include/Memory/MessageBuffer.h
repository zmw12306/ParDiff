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

#ifndef MEMORY_MESSAGEBUFFER_H
#define MEMORY_MESSAGEBUFFER_H

#include "Memory/MemoryBlock.h"
#include "Support/Z3.h"

class MessageBuffer : public MemoryBlock {
private:
    z3::expr Data;
    std::vector<AbstractValue *> VarIDAbsVal;

    /// in some rare cases, developers reuse the message buffer, e.g., tcp in lwip
    /// but the store dominates all uses
    /// todo we may need to check if the domination always holds. it should be, otherwise,
    ///  some bugs may be in the implementation
    /// todo the variable offset may be (almost) equivalent but in different style,
    ///  e.g., zext(len.32 + 4.32, 64) vs. zext(len, 64) + 4.64, which needs more expression rewriting
    std::map<z3::expr, z3::expr, Z3::less_than> VariableOffsetStore;

public:
    MessageBuffer(Type *Ty, unsigned Num = 1);

    ~MessageBuffer() override;

    AbstractValue *at(size_t ID) override;

    AbstractValue *at(const z3::expr &ID) override;

    z3::expr at(const z3::expr &Start, size_t Size, bool Swap = false);

    void gc();

    void store(const z3::expr &Val, const z3::expr Offset);

private:
    const z3::expr &data();

    bool hasStored(const z3::expr &Offset, z3::expr &Result);

public:
    static bool classof(const MemoryBlock *M) {
        return M->getKind() == MK_Message;
    }
};

#endif //MEMORY_MESSAGEBUFFER_H
