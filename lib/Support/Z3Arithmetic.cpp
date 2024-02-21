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

#include "Z3Macro.h"

template<class ConstOp, class ExprOp>
static inline z3::expr arithmetic_with_one_of(const z3::expr &O1, const z3::expr &O2, ConstOp COp, ExprOp EOp) {
    assert(O1.is_bv() && O2.is_bv());
    auto Bitwidth = O1.get_sort().bv_size();
    assert(Bitwidth == O2.get_sort().bv_size());

    if (Z3::is_phi(O1) && !Z3::is_phi(O2)) {
        auto ResultVec = Z3::vec();
        for (unsigned I = 0; I < O1.num_args(); ++I) {
            ResultVec.push_back(arithmetic_with_one_of(O1.arg(I), O2, COp, EOp));
        }
        return Z3::make_phi(Z3::phi_id(O1), ResultVec);
    } else if (!Z3::is_phi(O1) && Z3::is_phi(O2)) {
        auto ResultVec = Z3::vec();
        for (unsigned I = 0; I < O2.num_args(); ++I) {
            ResultVec.push_back(arithmetic_with_one_of(O1, O2.arg(I), COp, EOp));
        }
        return Z3::make_phi(Z3::phi_id(O2), ResultVec);
    } else if (Z3::same_phi(O1, O2)) {
        auto ResultVec = Z3::vec();
        for (unsigned I = 0; I < O2.num_args(); ++I) {
            ResultVec.push_back(arithmetic_with_one_of(O1.arg(I), O2.arg(I), COp, EOp));
        }
        return Z3::make_phi(Z3::phi_id(O1), ResultVec);
    } else {
        uint64_t Const1;
        bool Op1Const = O1.is_numeral_u64(Const1);
        uint64_t Const2;
        bool Op2Const = O2.is_numeral_u64(Const2);
        if (Op1Const && Op2Const) {
            return Z3::bv_val(COp(Const1, Const2), Bitwidth);
        } else if (Z3::is_free(O1) || Z3::is_free(O2)) {
            return Z3::free_bv(O1.get_sort().bv_size());
        } else {
            return EOp(O1, O2);
        }
    }
}

template<class ConstOp, class ExprOp>
static inline z3::expr arithmetic_with_one_of(const z3::expr &O, ConstOp COp, ExprOp EOp) {
    assert(O.is_bv());
    if (Z3::is_phi(O)) {
        auto OpVec = Z3::vec();
        for (unsigned I = 0; I < O.num_args(); ++I) {
            OpVec.push_back(arithmetic_with_one_of(O.arg(I), COp, EOp));
        }
        return Z3::make_phi(Z3::phi_id(O), OpVec);
    } else {
        uint64_t Const;
        bool OpConst = O.is_numeral_u64(Const);
        if (OpConst) {
            return COp(Const);
        } else {
            return EOp(O);
        }
    }
}

template<class ExprOp>
static inline z3::expr arithmetic_with_one_of(const z3::expr &O, ExprOp EOp) {
    assert(O.is_bv());
    if (Z3::is_phi(O)) {
        auto OpVec = Z3::vec();
        for (unsigned I = 0; I < O.num_args(); ++I) {
            OpVec.push_back(arithmetic_with_one_of(O.arg(I), EOp));
        }
        return Z3::make_phi(Z3::phi_id(O), OpVec);
    } else {
        return EOp(O);
    }
}

template<class BvOp, class RelOp>
static inline z3::expr bv_op_with_ite(const z3::expr &E1, const z3::expr &E2, BvOp BO, RelOp RO) {
    if (E1.decl().decl_kind() == Z3_OP_ITE && E2.decl().decl_kind() == Z3_OP_ITE) {
        uint64_t C1, C2, C3, C4;
        auto E1A1 = E1.arg(1);
        auto E1A2 = E1.arg(2);
        if (Z3::is_numeral_u64(E1A1, C1) && Z3::is_numeral_u64(E1A2, C2)
            && Z3::is_numeral_u64(E2.arg(1), C3) && Z3::is_numeral_u64(E2.arg(2), C4)) {
            if ((C1 == 0 || C1 == 1)
                && (C2 == 0 || C2 == 1)
                && (C3 == 0 || C3 == 1)
                && (C4 == 0 || C4 == 1)) {
                auto Cond1 = E1.arg(0);
                if (C1 == 0) {
                    Cond1 = Z3::negation(Cond1);
                }
                auto Cond2 = E2.arg(0);
                if (C3 == 0) {
                    Cond2 = Z3::negation(Cond2);
                }
                return Z3::ite(RO(Cond1, Cond2),
                               Z3::bv_val(1, E1A1.get_sort().bv_size()),
                               Z3::bv_val(0, E1A1.get_sort().bv_size()));
            }
        }
    }
    return BO(E1, E2);
}

static inline int64_t to_signed(uint64_t V, uint64_t BvSize) {
    V = V << (64 - BvSize);
    V = ((int64_t) V) >> (64 - BvSize);
    return (int64_t) V;
}

z3::expr Z3::add(const z3::expr &O1, int I) {
    return Z3::add(O1, Z3::bv_val(I, O1.get_sort().bv_size()));
}

z3::expr Z3::add(const z3::expr &O1, const z3::expr &O2) {
    return arithmetic_with_one_of(
            O1,
            O2,
            [](uint64_t A, uint64_t B) { return A + B; },
            [](const z3::expr &A, const z3::expr &B) { return (A + B).simplify(); });
}

z3::expr Z3::sub(const z3::expr &O1, const z3::expr &O2) {
    return arithmetic_with_one_of(
            O1,
            O2,
            [](uint64_t A, uint64_t B) { return A - B; },
            [](const z3::expr &A, const z3::expr &B) { return (A - B).simplify(); });
}

z3::expr Z3::mul(const z3::expr &O1, const z3::expr &O2) {
    return arithmetic_with_one_of(
            O1,
            O2,
            [](uint64_t A, uint64_t B) { return A * B; },
            [](const z3::expr &A, const z3::expr &B) { return (A * B).simplify(); });
}

z3::expr Z3::udiv(const z3::expr &O1, const z3::expr &O2) {
    return arithmetic_with_one_of(
            O1,
            O2,
            [](uint64_t A, uint64_t B) { return A / B; },
            [](const z3::expr &A, const z3::expr &B) { return z3::udiv(A, B).simplify(); });
}

z3::expr Z3::sdiv(const z3::expr &O1, const z3::expr &O2) {
    uint64_t Bitwidth = O1.get_sort().bv_size();
    return arithmetic_with_one_of(
            O1,
            O2,
            [Bitwidth](uint64_t A, uint64_t B) { return to_signed(A, Bitwidth) / to_signed(B, Bitwidth); },
            [](const z3::expr &A, const z3::expr &B) { return (A / B).simplify(); });
}

z3::expr Z3::urem(const z3::expr &O1, const z3::expr &O2) {
    return arithmetic_with_one_of(
            O1,
            O2,
            [](uint64_t A, uint64_t B) { return A % B; },
            [](const z3::expr &A, const z3::expr &B) { return z3::urem(A, B).simplify(); });
}

z3::expr Z3::srem(const z3::expr &O1, const z3::expr &O2) {
    uint64_t Bitwidth = O1.get_sort().bv_size();
    return arithmetic_with_one_of(
            O1,
            O2,
            [Bitwidth](uint64_t A, uint64_t B) { return to_signed(A, Bitwidth) % to_signed(B, Bitwidth); },
            [](const z3::expr &A, const z3::expr &B) { return z3::srem(A, B).simplify(); });
}

z3::expr Z3::bvand(const z3::expr &O1, const z3::expr &O2) {
    return arithmetic_with_one_of(
            O1,
            O2,
            [](uint64_t A, uint64_t B) { return A & B; },
            [](const z3::expr &A, const z3::expr &B) {
                return bv_op_with_ite(A, B,
                                      [](const z3::expr &A, const z3::expr &B) { return (A & B).simplify(); },
                                      [](const z3::expr &A, const z3::expr &B) { return Z3::make_and(A, B); });
            });
}

z3::expr Z3::bvor(const z3::expr &O1, const z3::expr &O2) {
    return arithmetic_with_one_of(
            O1,
            O2,
            [](uint64_t A, uint64_t B) { return A | B; },
            [](const z3::expr &A, const z3::expr &B) {
                return bv_op_with_ite(A, B,
                                      [](const z3::expr &A, const z3::expr &B) { return (A | B).simplify(); },
                                      [](const z3::expr &A, const z3::expr &B) { return Z3::make_or(A, B); });
            });
}

z3::expr Z3::bvxor(const z3::expr &O1, const z3::expr &O2) {
    return arithmetic_with_one_of(
            O1,
            O2,
            [](uint64_t A, uint64_t B) { return A ^ B; },
            [](const z3::expr &A, const z3::expr &B) { return (A ^ B).simplify(); });
}

z3::expr Z3::shl(const z3::expr &O1, const z3::expr &O2) {
    return arithmetic_with_one_of(
            O1,
            O2,
            [](uint64_t A, uint64_t B) { return A << B; },
            [](const z3::expr &A, const z3::expr &B) { return z3::shl(A, B).simplify(); });
}

z3::expr Z3::lshr(const z3::expr &O1, const z3::expr &O2) {
    return arithmetic_with_one_of(
            O1,
            O2,
            [](uint64_t A, uint64_t B) { return A >> B; },
            [](const z3::expr &A, const z3::expr &B) { return z3::lshr(A, B).simplify(); });
}

z3::expr Z3::ashr(const z3::expr &O1, const z3::expr &O2) {
    uint64_t Bitwidth = O1.get_sort().bv_size();
    return arithmetic_with_one_of(
            O1,
            O2,
            [Bitwidth](uint64_t A, uint64_t B) { return to_signed(A, Bitwidth) >> to_signed(B, Bitwidth); },
            [](const z3::expr &A, const z3::expr &B) {
                if (A.decl().decl_kind() == Z3_OP_CONCAT) {
                    uint64_t Const;
                    if (Z3::is_numeral_u64(A.arg(0), Const) && !Const) {
                        // if the prefix is zero, ashr == lshr
                        // lshr's simplifying alg is more powerful
                        return z3::lshr(A, B).simplify();
                    }
                } else if (A.decl().decl_kind() == Z3_OP_ZERO_EXT) {
                    // if the prefix is zero, ashr == lshr
                    // lshr's simplifying alg is more powerful
                    return z3::lshr(A, B).simplify();
                }
                return z3::ashr(A, B).simplify();
            });
}

z3::expr Z3::concat(const z3::expr &O1, const z3::expr &O2) {
    if (Z3::is_free(O1) || Z3::is_free(O2))
        return Z3::free_bv(O1.get_sort().bv_size() + O2.get_sort().bv_size());
    if (Z3::is_phi(O1) && !Z3::is_phi(O2)) {
        auto RetVec = Z3::vec();
        for (unsigned I = 0; I < O1.num_args(); ++I) {
            RetVec.push_back(concat(O1.arg(I), O2));
        }
        return Z3::make_phi(Z3::phi_id(O1), RetVec);
    } else if (!Z3::is_phi(O1) && Z3::is_phi(O2)) {
        auto RetVec = Z3::vec();
        for (unsigned I = 0; I < O2.num_args(); ++I) {
            RetVec.push_back(concat(O1, O2.arg(I)));
        }
        return Z3::make_phi(Z3::phi_id(O2), RetVec);
    } else if (!Z3::is_phi(O1) && !Z3::is_phi(O2)) {
        return z3::concat(O1, O2).simplify();
    } else if (Z3::phi_id(O1) == Z3::phi_id(O2)) {
        auto RetVec = Z3::vec();
        for (unsigned I = 0; I < O2.num_args(); ++I) {
            RetVec.push_back(concat(O1.arg(I), O2.arg(I)));
        }
        return Z3::make_phi(Z3::phi_id(O2), RetVec);
    }
    return z3::concat(O1, O2).simplify();
}

z3::expr Z3::concat(const z3::expr_vector &V) {
    bool RetFree = false;
    unsigned BW = 0;
    for (unsigned K = 0; K < V.size(); ++K) {
        auto E = V[K];
        if (!RetFree && Z3::is_free(E)) RetFree = true;
        BW += E.get_sort().bv_size();
    }
    if (RetFree) return Z3::free_bv(BW);
    return z3::concat(V).simplify();
}

z3::expr Z3::concat(std::vector<z3::expr> &V) {
     bool RetFree = false;
     z3::expr_vector Vec = Z3::vec();
     unsigned BW = 0;
     for (unsigned K = 0; K < V.size(); ++K) {
         auto E = V[K];
         if (!RetFree && Z3::is_free(E)) RetFree = true;
         BW += E.get_sort().bv_size();
         Vec.push_back(E);
     }
     if (RetFree) return Z3::free_bv(BW);
     return z3::concat(Vec).simplify();
 }

z3::expr Z3::extract(const z3::expr &E, unsigned H, unsigned L) {
    return arithmetic_with_one_of(
            E,
            [H, L](uint64_t A) { return Z3::bv_val(A << (63 - H) >> (63 - H + L), H - L + 1); },
            [H, L](const z3::expr &A) {
                return Z3::is_free(A) ? Z3::free_bv(H - L + 1) : A.extract(H, L).simplify();
            });
}

z3::expr Z3::extract_byte(const z3::expr &E, unsigned ByteIndex) {
    // ByteIndex = 0 => the least significant byte
    assert(ByteIndex < E.get_sort().bv_size() / 8);
    return Z3::extract(E, (ByteIndex + 1) * 8 - 1, ByteIndex * 8);
}

z3::expr Z3::extract_byte(const z3::expr &E, unsigned ByteIndex, unsigned NumBytes) {
    // ByteIndex = 0 => the least significant byte
    assert(NumBytes > 0);
    assert(ByteIndex < E.get_sort().bv_size() / 8);
    assert(ByteIndex + NumBytes - 1 < E.get_sort().bv_size() / 8);
    return Z3::extract(E, (ByteIndex + NumBytes) * 8 - 1, ByteIndex * 8);
}

z3::expr Z3::byteswap(const z3::expr &E) {
    assert(E.is_bv());
    auto Bitwidth = E.get_sort().bv_size();
    assert(Bitwidth % 16 == 0);

    return arithmetic_with_one_of(
            E,
            [Bitwidth](const z3::expr &E) {
                if (Z3::is_free(E)) return Z3::free_bv(Bitwidth);
                z3::expr_vector Vec = Z3::vec();
                for (unsigned I = 0; I < Bitwidth; I += 8) {
                    Vec.push_back(E.extract(I + 7, I).simplify());
                }
                return z3::concat(Vec).simplify();
            });
}