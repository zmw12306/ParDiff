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


#include "Support/DL.h"

static const DataLayout *Layout = nullptr;
static unsigned PointerBytewidth = 0;

void DL::initialize(const DataLayout &D) {
    Layout = &D;
    PointerBytewidth = D.getPointerSize();
    assert (!DL::isBigEndian() && "We assume a little endian bitcode! This is a big endian bitcode!");
}

unsigned DL::getNumBits(Type *Ty) {
    return Layout->getTypeSizeInBits(Ty);
}

unsigned DL::getNumBytes(Type *Ty) {
    return Layout->getTypeAllocSize(Ty);
}

unsigned DL::getPointerNumBytes() {
    return PointerBytewidth;
}

const StructLayout *DL::getStructLayout(Type *Ty) {
    assert(Ty->isStructTy());
    return Layout->getStructLayout((StructType *) Ty);
}

static Constant *getElement(Constant *C, unsigned I) {
    auto *CT = C->getType();
    if (auto *AggZero = dyn_cast<ConstantAggregateZero>(C)) {
        if (CT->isArrayTy()) {
            return AggZero->getSequentialElement();
        } else if (CT->isStructTy()) {
            return AggZero->getStructElement(I);
        } else {
            errs() << *C << "\n";
            llvm_unreachable("Error: Unsupported type!");
        }
    } else if (auto *ConstAggregate = dyn_cast<ConstantAggregate>(C)) {
        return ConstAggregate->getAggregateElement(I);
    } else if (auto *ConstDataSeq = dyn_cast<ConstantDataSequential>(C)) {
        return ConstDataSeq->getElementAsConstant(I);
    } else {
        errs() << *C << "\n";
        llvm_unreachable("Error: Unsupported type!");
    }
}

void DL::flatten(Constant *Const, std::vector<Constant *> &Ret) {
    auto *Ty = Const->getType();
    switch (Ty->getTypeID()) {
        case Type::PointerTyID:
        case Type::IntegerTyID:
        case Type::HalfTyID:
        case Type::BFloatTyID:
        case Type::FloatTyID:
        case Type::DoubleTyID:
        case Type::X86_MMXTyID:
        case Type::PPC_FP128TyID:
        case Type::FP128TyID:
        case Type::X86_AMXTyID:
        case Type::X86_FP80TyID:
            Ret.push_back(Const);
            break;
        case Type::ArrayTyID: {
            auto NumElmt = ((ArrayType *) Ty)->getNumElements();
            for (unsigned I = 0; I < NumElmt; ++I) {
                auto *ElmtConst = getElement(Const, I);
                std::vector<Constant *> FlattenedValues;
                flatten(ElmtConst, FlattenedValues);
                Ret.insert(Ret.end(), FlattenedValues.begin(), FlattenedValues.end());
            }
        }
            break;
        case Type::StructTyID: {
            auto *StrTy = (StructType *) Ty;
            const StructLayout *SL = DL::getStructLayout(StrTy);
            unsigned NumElements = StrTy->getNumElements();
            for (unsigned I = 0; I < NumElements; ++I) {
                auto *ElmtTy = StrTy->getElementType(I);
                auto *ElmtConst = getElement(Const, I);
                assert(ElmtTy == ElmtConst->getType());
                std::vector<Constant *> FlattenedAVs;
                flatten(ElmtConst, FlattenedAVs);
                Ret.insert(Ret.end(), FlattenedAVs.begin(), FlattenedAVs.end());

                unsigned Offset = SL->getElementOffset(I);
                unsigned PaddingBytes;
                if (I == NumElements - 1) {
                    PaddingBytes = DL::getNumBytes(StrTy) - Offset - DL::getNumBytes(ElmtTy);
                } else {
                    unsigned NextOffset = SL->getElementOffset(I + 1);
                    PaddingBytes = NextOffset - Offset - DL::getNumBytes(ElmtTy);
                }
                for (unsigned J = 0; J < PaddingBytes; ++J) {
                    // add a padding byte
                    Ret.push_back(ConstantInt::get(Type::getInt8Ty(Const->getContext()), 0));
                }
            }
        }
            break;
        case Type::FixedVectorTyID:
        case Type::ScalableVectorTyID:
        case Type::LabelTyID:
        default:
            llvm_unreachable("Error: Unsupported type");
    }
}

void DL::flatten(Type *Ty, std::vector<Type *> &Ret, bool FlattenArray) {
    switch (Ty->getTypeID()) {
        case Type::PointerTyID:
        case Type::IntegerTyID:
        case Type::HalfTyID:
        case Type::BFloatTyID:
        case Type::FloatTyID:
        case Type::DoubleTyID:
        case Type::X86_MMXTyID:
        case Type::PPC_FP128TyID:
        case Type::FP128TyID:
        case Type::X86_AMXTyID:
        case Type::X86_FP80TyID:
            Ret.push_back(Ty);
            break;
        case Type::ArrayTyID: {
            auto *ArrTy = (ArrayType *) Ty;
            auto *ElmtTy = ArrTy->getElementType();
            auto NumElmt = ArrTy->getNumElements();
            // num element may be 0, which often occurs at the end of a struct
            // such a 0-sized array is often used to compute pointer offsets
            if (NumElmt > 0) {
                if (FlattenArray) {
                    std::vector<Type *> FlattenedTypes;
                    flatten(ElmtTy, FlattenedTypes, FlattenArray);
                    Ret.insert(Ret.end(), FlattenedTypes.begin(), FlattenedTypes.end());
                    auto Size = Ret.size();
                    for (unsigned I = 1; I < NumElmt; ++I) {
                        for (unsigned J = 0; J < Size; ++J) {
                            Ret.push_back(Ret[J]);
                        }
                    }
                } else {
                    Ret.push_back(Ty);
                }
            }
        }
            break;
        case Type::StructTyID: {
            auto *StrTy = (StructType *) Ty;
            const StructLayout *SL = DL::getStructLayout(StrTy);
            unsigned NumElements = StrTy->getNumElements();
            for (unsigned I = 0; I < NumElements; ++I) {
                auto *ElmtTy = StrTy->getElementType(I);
                std::vector<Type *> FlattenedTypes;
                flatten(ElmtTy, FlattenedTypes, FlattenArray);
                Ret.insert(Ret.end(), FlattenedTypes.begin(), FlattenedTypes.end());

                unsigned Offset = SL->getElementOffset(I);
                unsigned PaddingBytes;
                if (I == NumElements - 1) {
                    PaddingBytes = DL::getNumBytes(StrTy) - Offset - DL::getNumBytes(ElmtTy);
                } else {
                    unsigned NextOffset = SL->getElementOffset(I + 1);
                    PaddingBytes = NextOffset - Offset - DL::getNumBytes(ElmtTy);
                }
                for (unsigned J = 0; J < PaddingBytes; ++J) {
                    // add a padding byte
                    Ret.push_back(Type::getInt8Ty(Ty->getContext()));
                }
            }
        }
            break;
        case Type::FixedVectorTyID:
        case Type::ScalableVectorTyID:
        case Type::LabelTyID:
        default:
            llvm_unreachable("Error: Unsupported type");
    }
}

static void nameType(DIType *D1, DIType *D2) {
    if (!D1) return;

    StringRef D1Name = D1->getName(), D2Name = D2->getName();
    if (D1Name.empty() && !D2Name.empty()) {
        auto &Ctx = D1->getContext();
        D1->replaceOperandWith(2, MDString::get(Ctx, D2Name)); // 2 is the index of name, see DIType::getName()
    } else if (!D1Name.empty() && D2Name.empty()) {
        auto &Ctx = D1->getContext();
        D2->replaceOperandWith(2, MDString::get(Ctx, D1Name)); // 2 is the index of name, see DIType::getName()
    }
}

DIType *DL::stripDITypeCast(DIType *DIVTy) {
    while (DIVTy && (DIVTy->getTag() == dwarf::DW_TAG_typedef || DIVTy->getTag() == dwarf::DW_TAG_const_type)) {
        assert(isa<DIDerivedType>(DIVTy));
        auto *NextDIVTy = ((DIDerivedType *) DIVTy)->getBaseType();
        nameType(NextDIVTy, DIVTy);
        DIVTy = NextDIVTy;
    }
    return DIVTy;
}

static void flatten(DICompositeType *CompositeTy, std::vector<CompositeTypeElement> &Ret, std::string NamePrefix,
                    uint64_t BaseOffset) {
    auto ElmtArray = CompositeTy->getElements();
    for (unsigned int Idx = 0; Idx < ElmtArray->getNumOperands(); Idx++) {
        DIType *DTy = dyn_cast<DIType>(ElmtArray->getOperand(Idx).get());
        assert(DTy);
        assert(DTy->getTag() == dwarf::DW_TAG_member);
        assert(!DTy->isStaticMember() && "Do not support C++!");
        auto DTyName = NamePrefix + "." + DTy->getName().str();
        auto DTySize = DTy->getSizeInBits();
        auto DTyOffs = DTy->getOffsetInBits() + BaseOffset;
        DTy = DL::stripDITypeCast(cast<DIDerivedType>(DTy)->getBaseType());
        auto *CTy = dyn_cast_or_null<DICompositeType>(DTy);
        if (CTy && CTy->getTag() == dwarf::DW_TAG_structure_type) {
            std::vector<CompositeTypeElement> CTyRet;
            flatten(CTy, CTyRet, DTyName, DTyOffs);
            Ret.insert(Ret.end(), CTyRet.begin(), CTyRet.end());
        } else {
            Ret.push_back({DTyName, DTySize, DTyOffs});
        }
    }
}

void DL::flatten(DICompositeType *CompositeTy, std::vector<CompositeTypeElement> &Ret) {
    auto CompositeTyName = CompositeTy->getName();
    ::flatten(CompositeTy, Ret, CompositeTyName.str(), 0);
}

bool DL::isBigEndian() {
    return Layout->isBigEndian();
}

DIType *DL::getDIPointerType(DIType *BaseTy) {
    return DIDerivedType::get(BaseTy->getContext(),
                              dwarf::DW_TAG_pointer_type,
                              BaseTy->getName(),
                              BaseTy->getFile(),
                              BaseTy->getLine(),
                              BaseTy->getScope(),
                              stripDITypeCast(BaseTy),
                              DL::getPointerNumBytes() * 8,
                              0,
                              0,
                              0,
                              BaseTy->getFlags()
    );
}
