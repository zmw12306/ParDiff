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


#ifndef SUPPORT_DL_H
#define SUPPORT_DL_H

#include <llvm/IR/Constants.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/DebugInfoMetadata.h>

using namespace llvm;

typedef struct CompositeTypeElement {
    std::string FieldName;
    uint64_t FieldBitwidth;
    uint64_t FieldOffset;
} CompositeTypeElement;

class DL {
public:
    /// call only at initialization
    static void initialize(const DataLayout &);

    /// @{
    static unsigned getNumBits(Type *Ty);

    static unsigned getNumBytes(Type *Ty);

    static unsigned getPointerNumBytes();

    static const StructLayout *getStructLayout(Type *Ty);
    /// @}

    static bool isBigEndian();

    static void flatten(Constant *, std::vector<Constant *> &);

    static void flatten(Type *, std::vector<Type *> &, bool = true);

    static DIType *stripDITypeCast(DIType *DIVTy);

    static void flatten(DICompositeType *, std::vector<CompositeTypeElement> &);

    static DIType *getDIPointerType(DIType *BaseTy);
};

#endif //SUPPORT_DL_H
