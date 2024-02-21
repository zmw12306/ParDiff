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

#include "Memory/AbstractValue.h"
#include "Memory/MemoryBlock.h"
#include "Memory/MessageBuffer.h"
#include "Support/DL.h"

AbstractValue::~AbstractValue() = default;

AbstractValue::AbstractValueKind AbstractValue::getKind() const {
    return Kind;
}

StringRef AbstractValue::getKindName() const {
    return Kind == AVK_Scalar ? "AbstractScalar" : "AbstractAddress";
}

void ScalarValue::assign(AbstractValue *AV) {
    assert(bytewidth() == AV->bytewidth());
    set(AV->value());
}

std::string ScalarValue::str() {
    if (poison()) return std::string("cu.") + std::to_string(bytewidth());

    std::string Content;
    int64_t X;
    if (int64(X)) {
        Content.append(std::to_string(X));
    } else {
        Content.append(Z3::to_string(value()));
    }
    Content.append(".");
    return Content.append(std::to_string(bytewidth()));
}

void AddressValue::assign(MemoryBlock *Addr) {
    this->BaseVec.clear();
    this->OffsetVec.clear();
    this->BaseVec.push_back(Addr);
    this->OffsetVec.push_back(Z3::bv_val(0, DL::getPointerNumBytes() * 8));
}

void AddressValue::assign(AbstractValue *Src) {
    if (auto *AV = dyn_cast_or_null<AddressValue>(Src)) {
        this->BaseVec = AV->BaseVec;
        this->OffsetVec = AV->OffsetVec;
    } else {
        llvm_unreachable("Error: assigning a scalar to an address");
    }
}

void AddressValue::add(AbstractValue *AV) {
    auto *Addr = dyn_cast_or_null<AddressValue>(AV);
    assert(Addr);
    if (BaseVec.empty()) {
        BaseVec = Addr->BaseVec;
        OffsetVec = Addr->OffsetVec;
    } else {
        unsigned OldSize = BaseVec.size();
        for (unsigned J = 0; J < Addr->BaseVec.size(); ++J) {
            auto *NewMem = Addr->BaseVec[J];
            auto &NewOffset = Addr->OffsetVec[J];
            bool NeedToAdd = true;
            for (unsigned I = 0; I < OldSize; ++I) {
                auto *OldMem = BaseVec[I];
                auto &OldOffset = OffsetVec[I];
                if (NewMem == OldMem && Z3::same(NewOffset, OldOffset)) {
                    NeedToAdd = false;
                    break;
                } else if (NewMem == OldMem && isa_and_nonnull<MessageBuffer>(NewMem)) {
                    NeedToAdd = false;
                    OldOffset = Z3::ite(Z3::free_bool(), NewOffset, OldOffset);
                    break;
                }
            }
            if (NeedToAdd) {
                BaseVec.push_back(Addr->BaseVec[J]);
                OffsetVec.push_back(Addr->OffsetVec[J]);
            }
        }
    }
}

void AddressValue::removeNull() {
    while (!BaseVec.empty() && !BaseVec.back()) {
        BaseVec.pop_back();
        OffsetVec.pop_back();
    }
    for (unsigned I = 0; I < size(); ++I) {
        if (!BaseVec[I]) {
            BaseVec[I] = BaseVec.back();
            OffsetVec[I] = OffsetVec.back();
            BaseVec.pop_back();
            OffsetVec.pop_back();

            while (!BaseVec.empty() && !BaseVec.back()) {
                BaseVec.pop_back();
                OffsetVec.pop_back();
            }
        }
    }
}

void AddressValue::forward(ScalarValue *Index, uint64_t Sz) {
    // before performing forward, we have regarded them as non-null pointers
    removeNull();
    if (poison()) return;

    int64_t Id;
    if (Index->int64(Id)) {
        if (Id < 0) {
            mkpoison();
        } else {
            forward(Id * Sz);
        }
    } else if (Index->poison()) {
        mkpoison();
    } else {
        if (Sz == 0) {
            forward(0);
        } else if (Sz == 1) {
            forward(Index->value());
        } else {
            forward(Index->value() * (int) Sz);
        }
    }
}

void AddressValue::forward(uint64_t Steps) {
    // before performing forward, we have regarded them as non-null pointers
    removeNull();
    if (poison()) return;
    if (Steps == 0) return;

    for (auto K = 0; K < size(); ++K) {
        doForward(BaseVec[K], OffsetVec[K], Steps);
    }

    // doForward may intentionally set some address to null
    // when doForward exceeds the boundary of a memory space
    removeNull();
}

void AddressValue::forward(const z3::expr &Steps) {
    // before performing forward, we have regarded them as non-null pointers
    removeNull();
    if (poison()) return;
    for (auto K = 0; K < size(); ++K) {
        auto &Base = BaseVec[K];
        if (isa<MessageBuffer>(Base)) {
            uint64_t OffNum;
            if (OffsetVec[K].is_numeral_u64(OffNum) && OffNum == 0) {
                OffsetVec[K] = Steps;
            } else {
                OffsetVec[K] = Z3::add(OffsetVec[K], Steps);
            }
        } else {
            // just regard steps as zero
        }
    }
}

void AddressValue::doForward(MemoryBlock *&Addr, z3::expr &Off, uint64_t Steps) {
    assert(Addr && "we must have a valid base address!");
    uint64_t ConstOffset;
    if (!Off.is_numeral_u64(ConstOffset)) {
        // find a symbolic offset, then it must be a message buffer
        assert(isa<MessageBuffer>(Addr));
        Off = Z3::add(Off, Z3::bv_val(Steps, Off.get_sort().bv_size()));
        return;
    }

    bool Array = true;
    unsigned LastByte = 0;
    while (true) {
        auto *MemV = Addr->at(ConstOffset);
        if (!MemV) {
            // we reach the boundary of a memory block
            if (Array) {
                // if this is an array, let us reset
                // do nothing, because Off is not changed
            } else {
                Addr = nullptr; // to make it poison
            }
            break;
        }
        ConstOffset += MemV->bytewidth();
        if (Steps == 0)
            break;

        unsigned CurrentByte = MemV->bytewidth();
        if (LastByte != 0 && Array) { Array = LastByte == CurrentByte; }
        LastByte = CurrentByte;
        if (Steps < CurrentByte) {
            Addr = nullptr; // to make it poison
            break;
        } else {
            Steps -= CurrentByte;
        }
        if (Steps == 0) {
            Off = Z3::bv_val(ConstOffset, Off.get_sort().bv_size());
        }
    }
}

std::string AddressValue::str() {
    if (poison())
        return "au.8";

    std::string Content("{ ");
    raw_string_ostream Str(Content);
    for (auto K = 0; K < size(); ++K) {
        int64_t X;
        auto &Offset = offset(K);
        auto *Base = base(K);
        if (Base) {
            if (Base->getKind() == MemoryBlock::MK_Stack) {
                Content.append("S.");
            } else if (Base->getKind() == MemoryBlock::MK_Heap) {
                Content.append("H.");
            } else if (Base->getKind() == MemoryBlock::MK_Global) {
                Content.append("G.");
            } else {
                Content.append("M.");
            }
            Str << Base;

            if (Offset.is_numeral_i64(X)) {
                Content.append(".").append(std::to_string(X));
            } else {
                Content.append(".").append(Z3::to_string(Offset));
            }
        } else {
            Content.append("nil");
        }

        if (K != size() - 1) {
            Content.append(", ");
        }
    }
    return Content.append(" }");
}

namespace abs_value {
    // start of cast operations

    void trunc(AbstractValue *Dst, AbstractValue *Src) {
        if (Src->poison()) return;
        Dst->set(Z3::trunc(Src->value(), Dst->bytewidth() * 8));
    }

    void sext(AbstractValue *Dst, AbstractValue *Src) {
        if (Src->poison()) return;
        Dst->set(Z3::sext(Src->value(), Dst->bytewidth() * 8));
    }

    void zext(AbstractValue *Dst, AbstractValue *Src) {
        if (Src->poison()) return;
        Dst->set(Z3::zext(Src->value(), Dst->bytewidth() * 8));
    }

    // end of cast operations
    // start of arithmetic operations

    void neg(AbstractValue *Dst, AbstractValue *Val) {
        ScalarValue Zero(Val->bytewidth(), Z3::bv_val(0, Val->bytewidth() * 8));
        sub(Dst, &Zero, Val);
    }

    void add(AbstractValue *Dst, AbstractValue *A1, AbstractValue *A2) {
        if (A1->poison() || A2->poison()) return;
        auto &O1 = A1->value();
        auto &O2 = A2->value();
        Dst->set(Z3::add(O1, O2));
    }

    void sub(AbstractValue *Dst, AbstractValue *A1, AbstractValue *A2) {
        if (A1->poison() || A2->poison()) return;
        auto &O1 = A1->value();
        auto &O2 = A2->value();
        Dst->set(Z3::sub(O1, O2));
    }

    void mul(AbstractValue *Dst, AbstractValue *A1, AbstractValue *A2) {
        if (A1->poison() || A2->poison()) return;
        auto &O1 = A1->value();
        auto &O2 = A2->value();
        Dst->set(Z3::mul(O1, O2));
    }

    void udiv(AbstractValue *Dst, AbstractValue *A1, AbstractValue *A2) {
        if (A1->poison() || A2->poison()) return;
        auto &O1 = A1->value();
        auto &O2 = A2->value();
        Dst->set(Z3::udiv(O1, O2));
    }

    void sdiv(AbstractValue *Dst, AbstractValue *A1, AbstractValue *A2) {
        if (A1->poison() || A2->poison()) return;
        auto &O1 = A1->value();
        auto &O2 = A2->value();
        Dst->set(Z3::sdiv(O1, O2));
    }

    void urem(AbstractValue *Dst, AbstractValue *A1, AbstractValue *A2) {
        if (A1->poison() || A2->poison()) return;
        auto &O1 = A1->value();
        auto &O2 = A2->value();
        Dst->set(Z3::urem(O1, O2));
    }

    void srem(AbstractValue *Dst, AbstractValue *A1, AbstractValue *A2) {
        if (A1->poison() || A2->poison()) return;
        auto &O1 = A1->value();
        auto &O2 = A2->value();
        Dst->set(Z3::srem(O1, O2));
    }

    void bvand(AbstractValue *Dst, AbstractValue *A1, AbstractValue *A2) {
        if (A1->poison() || A2->poison()) return;
        auto &O1 = A1->value();
        auto &O2 = A2->value();
        Dst->set(Z3::bvand(O1, O2));
    }

    void bvor(AbstractValue *Dst, AbstractValue *A1, AbstractValue *A2) {
        if (A1->poison() || A2->poison()) return;
        auto &O1 = A1->value();
        auto &O2 = A2->value();
        Dst->set(Z3::bvor(O1, O2));
    }

    void bvxor(AbstractValue *Dst, AbstractValue *A1, AbstractValue *A2) {
        if (A1->poison() || A2->poison()) return;
        auto &O1 = A1->value();
        auto &O2 = A2->value();
        Dst->set(Z3::bvxor(O1, O2));
    }

    void shl(AbstractValue *Dst, AbstractValue *A1, AbstractValue *A2) {
        if (A1->poison() || A2->poison()) return;
        auto &O1 = A1->value();
        auto &O2 = A2->value();
        Dst->set(Z3::shl(O1, O2));
    }

    void ashr(AbstractValue *Dst, AbstractValue *A1, AbstractValue *A2) {
        if (A1->poison() || A2->poison()) return;
        auto &O1 = A1->value();
        auto &O2 = A2->value();
        Dst->set(Z3::ashr(O1, O2));
    }

    void lshr(AbstractValue *Dst, AbstractValue *A1, AbstractValue *A2) {
        if (A1->poison() || A2->poison()) return;
        auto &O1 = A1->value();
        auto &O2 = A2->value();
        Dst->set(Z3::lshr(O1, O2));
    }

    // end of arithmetic operations
    // start of comparing operations

    void slt(AbstractValue *Dst, AbstractValue *A1, AbstractValue *A2) {
        sgt(Dst, A2, A1);
    }

    void sle(AbstractValue *Dst, AbstractValue *A1, AbstractValue *A2) {
        sge(Dst, A2, A1);
    }

    void sgt(AbstractValue *Dst, AbstractValue *A1, AbstractValue *A2) {
        if (A1->poison() || A2->poison()) return;
        z3::expr &O1 = A1->value();
        z3::expr &O2 = A2->value();
        auto Ret = Z3::sgt(O1, O2);
        Dst->set(Z3::bool_to_bv(Ret, Dst->bytewidth() * 8));
    }

    void sge(AbstractValue *Dst, AbstractValue *A1, AbstractValue *A2) {
        if (A1->poison() || A2->poison()) return;
        z3::expr &O1 = A1->value();
        z3::expr &O2 = A2->value();
        auto Ret = Z3::sge(O1, O2);
        Dst->set(Z3::bool_to_bv(Ret, Dst->bytewidth() * 8));
    }

    void ult(AbstractValue *Dst, AbstractValue *A1, AbstractValue *A2) {
        ugt(Dst, A2, A1);
    }

    void ule(AbstractValue *Dst, AbstractValue *A1, AbstractValue *A2) {
        uge(Dst, A2, A1);
    }

    void ugt(AbstractValue *Dst, AbstractValue *A1, AbstractValue *A2) {
        if (A1->poison() || A2->poison()) return;
        z3::expr &O1 = A1->value();
        z3::expr &O2 = A2->value();
        auto Ret = Z3::ugt(O1, O2);
        Dst->set(Z3::bool_to_bv(Ret, Dst->bytewidth() * 8));
    }

    void uge(AbstractValue *Dst, AbstractValue *A1, AbstractValue *A2) {
        if (A1->poison() || A2->poison()) return;
        z3::expr &O1 = A1->value();
        z3::expr &O2 = A2->value();
        auto Ret = Z3::uge(O1, O2);
        Dst->set(Z3::bool_to_bv(Ret, Dst->bytewidth() * 8));
    }

    void eq(AbstractValue *Dst, AbstractValue *A1, AbstractValue *A2) {
        if (A1->poison() || A2->poison()) return;
        z3::expr &O1 = A1->value();
        z3::expr &O2 = A2->value();
        auto Ret = Z3::eq(O1, O2);
        Dst->set(Z3::bool_to_bv(Ret, Dst->bytewidth() * 8));
    }

    void ne(AbstractValue *Dst, AbstractValue *A1, AbstractValue *A2) {
        if (A1->poison() || A2->poison()) return;
        z3::expr &O1 = A1->value();
        z3::expr &O2 = A2->value();
        auto Ret = Z3::ne(O1, O2);
        Dst->set(Z3::bool_to_bv(Ret, Dst->bytewidth() * 8));
    }

    // end of comparing operations
}
