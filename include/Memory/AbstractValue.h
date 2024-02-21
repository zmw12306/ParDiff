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

#ifndef MEMORY_ABSTRACTVALUE_H
#define MEMORY_ABSTRACTVALUE_H

#include <llvm/Support/Casting.h>
#include <z3++.h>
#include "Support/DL.h"
#include "Support/Z3.h"

#define DEFAULT_IMPL {                                                 \
        errs() << "Type :" << getKindName() << "\n";                   \
        llvm_unreachable("Error: not working for this type!");         \
    }

using namespace llvm;

class MemoryBlock;

class AbstractValue {
public:
    enum AbstractValueKind {
        AVK_Scalar,
        AVK_Address,
    };

private:
    AbstractValueKind Kind;

public:
    explicit AbstractValue(AbstractValueKind K) : Kind(K) {}

    virtual ~AbstractValue() = 0;

    [[nodiscard]] AbstractValueKind getKind() const;

    [[nodiscard]] StringRef getKindName() const;

    /// common interfaces for all value types
    /// @{
    /// a value we do not care about
    virtual bool poison() = 0;

    /// make a value poison
    virtual void mkpoison() = 0;

    /// the bytes used for storing the value, i1 -> 1 byte; i32 -> 4 bytes
    virtual unsigned bytewidth() = 0;

    virtual void assign(AbstractValue *) = 0;

    virtual std::string str() = 0;

    virtual void zeroInitialize() = 0;

    virtual AbstractValue *clone() = 0;
    /// @}

    /// only work for scalar
    /// @{
    virtual void set(const z3::expr &) DEFAULT_IMPL

    virtual z3::expr &value() DEFAULT_IMPL

    virtual bool int64(int64_t &) DEFAULT_IMPL

    virtual bool uint64(uint64_t &) DEFAULT_IMPL
    /// @}

    /// only work for address
    /// @{
    virtual z3::expr &offset(size_t) DEFAULT_IMPL

    virtual MemoryBlock *base(size_t) DEFAULT_IMPL

    virtual size_t size() DEFAULT_IMPL

    virtual void add(AbstractValue *) DEFAULT_IMPL
    /// @}
};

class ScalarValue : public AbstractValue {
private:
    z3::expr Value;
    unsigned Bytewidth;

public:
    explicit ScalarValue(unsigned Bytes) : AbstractValue(AVK_Scalar), Bytewidth(Bytes),
                                           Value(Z3::free_bv(Bytes * 8)) {}

    explicit ScalarValue(unsigned Bytes, const z3::expr &Val) : AbstractValue(AVK_Scalar),
                                                                Bytewidth(Bytes), Value(Val) {
        assert(Val.is_bv());
        assert(Val.get_sort().bv_size() == Bytes * 8);
    }

    ~ScalarValue() override = default;

    bool poison() override {
        return Z3::is_free(Value);
    }

    void mkpoison() override {
        Value = Z3::free_bv(Bytewidth * 8);
    }

    unsigned bytewidth() override {
        return Bytewidth;
    }

    z3::expr &value() override {
        return Value;
    }

    void set(const z3::expr &Val) override {
        assert(Bytewidth * 8 == Val.get_sort().bv_size());
        Value = Val;
    }

    bool int64(int64_t &I) override {
        if (poison()) return false;
        if (Z3::is_numeral_i64(Value, I)) {
            return true;
        }
        return false;
    }

    bool uint64(uint64_t &I) override {
        if (poison()) return false;
        if (Value.is_numeral_u64(I)) {
            return true;
        }
        return false;
    }

    void zeroInitialize() override {
        Value = Z3::bv_val(0, bytewidth() * 8);
    }

    void assign(AbstractValue *) override;

    std::string str() override;

    AbstractValue *clone() override {
        auto *Ret = new ScalarValue(Bytewidth, Value);
        return Ret;
    }

public:
    static bool classof(const AbstractValue *AV) {
        return AV->getKind() == AVK_Scalar;
    }
};

// todo unify the representation of address value and scalar value
//  represent an address value as an z3::expr base(Mem's Addr) + offset
//  so that we can do basic arithmetic on pointers and use the phi representation
class AddressValue : public AbstractValue {
private:
    /// This abstract value may stand for several possible addresses
    /// @{
    std::vector<MemoryBlock *> BaseVec;
    std::vector<z3::expr> OffsetVec;
    /// @}

public:
    AddressValue() : AbstractValue(AVK_Address) {}

    explicit AddressValue(MemoryBlock *Base) : AbstractValue(AVK_Address) {
        BaseVec.push_back(Base);
        OffsetVec.push_back(Z3::bv_val(0, DL::getPointerNumBytes() * 8));
    }

    AddressValue(MemoryBlock *Base, const z3::expr &Off) : AbstractValue(AVK_Address) {
        BaseVec.push_back(Base);
        OffsetVec.push_back(Off);
    }

    ~AddressValue() override = default;

    bool poison() override {
        return BaseVec.empty();
    }

    void mkpoison() override {
        std::vector<MemoryBlock *>().swap(BaseVec);
        std::vector<z3::expr>().swap(OffsetVec);
    }

    unsigned bytewidth() override {
        return DL::getPointerNumBytes();
    }

    void add(AbstractValue *AV) override;

    z3::expr &offset(size_t I) override {
        assert(I < size());
        return OffsetVec[I];
    }

    MemoryBlock *base(size_t I) override {
        assert(I < size());
        return BaseVec[I];
    }

    size_t size() override {
        assert(BaseVec.size() == OffsetVec.size());
        return BaseVec.size();
    }

    void zeroInitialize() override {
        BaseVec.clear();
        OffsetVec.clear();
        BaseVec.push_back(nullptr);
        OffsetVec.push_back(Z3::bv_val(0, bytewidth() * 8));
    }

    AbstractValue *clone() override {
        auto *Ret = new AddressValue;
        Ret->BaseVec = BaseVec;
        Ret->OffsetVec = OffsetVec;
        return Ret;
    }

    std::string str() override;

    void assign(AbstractValue *) override;

    void assign(MemoryBlock *Addr);

    void forward(uint64_t);

    void forward(const z3::expr &);

    void forward(ScalarValue *Index, uint64_t);

private:
    void doForward(MemoryBlock *&Addr, z3::expr &Off, uint64_t Steps);

    void removeNull();

public:
    static bool classof(const AbstractValue *AV) {
        return AV->getKind() == AVK_Address;
    }
};

/// operations on abstract values, will return a new value that need to be deleted
namespace abs_value {
    void trunc(AbstractValue *, AbstractValue *);

    void sext(AbstractValue *, AbstractValue *);

    void zext(AbstractValue *, AbstractValue *);

    void neg(AbstractValue *, AbstractValue *);

    void add(AbstractValue *, AbstractValue *, AbstractValue *);

    void sub(AbstractValue *, AbstractValue *, AbstractValue *);

    void mul(AbstractValue *, AbstractValue *, AbstractValue *);

    void udiv(AbstractValue *, AbstractValue *, AbstractValue *);

    void sdiv(AbstractValue *, AbstractValue *, AbstractValue *);

    void urem(AbstractValue *, AbstractValue *, AbstractValue *);

    void srem(AbstractValue *, AbstractValue *, AbstractValue *);

    void bvand(AbstractValue *, AbstractValue *, AbstractValue *);

    void bvor(AbstractValue *, AbstractValue *, AbstractValue *);

    void bvxor(AbstractValue *, AbstractValue *, AbstractValue *);

    void shl(AbstractValue *, AbstractValue *, AbstractValue *);

    void ashr(AbstractValue *, AbstractValue *, AbstractValue *);

    void lshr(AbstractValue *, AbstractValue *, AbstractValue *);

    void slt(AbstractValue *, AbstractValue *, AbstractValue *);

    void slt(AbstractValue *, uint64_t, AbstractValue *);

    void slt(AbstractValue *, AbstractValue *, uint64_t);

    void sle(AbstractValue *, AbstractValue *, AbstractValue *);

    void sle(AbstractValue *, uint64_t, AbstractValue *);

    void sle(AbstractValue *, AbstractValue *, uint64_t);

    void sgt(AbstractValue *, AbstractValue *, AbstractValue *);

    void sgt(AbstractValue *, uint64_t, AbstractValue *);

    void sgt(AbstractValue *, AbstractValue *, uint64_t);

    void sge(AbstractValue *, AbstractValue *, AbstractValue *);

    void sge(AbstractValue *, uint64_t, AbstractValue *);

    void sge(AbstractValue *, AbstractValue *, uint64_t);

    void ult(AbstractValue *, AbstractValue *, AbstractValue *);

    void ult(AbstractValue *, uint64_t, AbstractValue *);

    void ult(AbstractValue *, AbstractValue *, uint64_t);

    void ule(AbstractValue *, AbstractValue *, AbstractValue *);

    void ugt(AbstractValue *, AbstractValue *, AbstractValue *);

    void uge(AbstractValue *, AbstractValue *, AbstractValue *);

    void eq(AbstractValue *, AbstractValue *, AbstractValue *);

    void ne(AbstractValue *, AbstractValue *, AbstractValue *);
}

#endif //MEMORY_ABSTRACTVALUE_H
