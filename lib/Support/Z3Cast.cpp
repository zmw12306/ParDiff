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

z3::expr Z3::trunc(const z3::expr &E, unsigned TargetBitwidth) {
    assert(E.is_bv());
    assert(E.get_sort().bv_size() >= TargetBitwidth);
    if (E.get_sort().bv_size() == TargetBitwidth) return E;

    uint64_t Const;
    if (E.decl().decl_kind() == Z3_OP_ITE) {
        return z3::ite(E.arg(0),
                       Z3::trunc(E.arg(1), TargetBitwidth),
                       Z3::trunc(E.arg(2), TargetBitwidth));
    } else if (is_phi(E)) {
        auto RetVec = Z3::vec();
        for (unsigned I = 0; I < E.num_args(); ++I) {
            RetVec.push_back(trunc(E.arg(I), TargetBitwidth));
        }
        return Z3::make_phi(Z3::phi_id(E), RetVec);
    } else if (Z3::is_numeral_u64(E, Const)) {
        Const = (Const << (64 - TargetBitwidth)) >> (64 - TargetBitwidth);
        return Z3::bv_val(Const, TargetBitwidth);
    } else {
        return E.extract(TargetBitwidth - 1, 0).simplify();
    }
}

z3::expr Z3::trunc_expression(const z3::expr &E, unsigned TargetBitwidth) {
    assert(E.is_bv());
    assert(E.get_sort().bv_size() >= TargetBitwidth);
    if (E.get_sort().bv_size() == TargetBitwidth) return E;

    auto TruncSize = E.get_sort().bv_size() - TargetBitwidth;
    if (Z3::is_phi(E)) {
        auto Vec = Z3::vec();
        for (unsigned K = 0; K < E.num_args(); ++K) {
            auto A = E.arg(K);
            auto TruncA = trunc_expression(A, TargetBitwidth);
            if (TruncA.get_sort().bv_size() != TargetBitwidth) return E;
            Vec.push_back(TruncA);
        }
        return Z3::make_phi(Z3::phi_id(E), Vec);
    } else {
        auto Decl = E.decl();
        auto DeclKind = Decl.decl_kind();
        switch (DeclKind) {
            case Z3_OP_ITE: {
                assert(E.num_args() == 3);
                auto A1 = Z3::trunc_expression(E.arg(1), TargetBitwidth);
                auto A2 = Z3::trunc_expression(E.arg(2), TargetBitwidth);
                if (A1.get_sort().bv_size() == TargetBitwidth && A2.get_sort().bv_size() == TargetBitwidth) {
                    return Z3::ite(E.arg(0), A1, A2);
                }
            }
                break;
            case Z3_OP_BNEG: {
                assert(E.num_args() == 1);
                auto A1 = Z3::trunc_expression(E.arg(0), TargetBitwidth);
                if (A1.get_sort().bv_size() == TargetBitwidth) {
                    return -A1;
                }
            }
                break;
            case Z3_OP_BADD: {
                assert(E.num_args() >= 2);
                auto A1 = Z3::trunc_expression(E.arg(0), TargetBitwidth);
                if (A1.get_sort().bv_size() != TargetBitwidth) return E;
                for (unsigned K = 1; K < E.num_args(); ++K) {
                    auto A2 = Z3::trunc_expression(E.arg(K), TargetBitwidth);
                    if (A2.get_sort().bv_size() != TargetBitwidth) return E;
                    A1 = Z3::add(A1, A2);
                }
                return A1;
            }
                break;
            case Z3_OP_BSUB: {
                assert(E.num_args() == 2);
                auto A1 = Z3::trunc_expression(E.arg(0), TargetBitwidth);
                auto A2 = Z3::trunc_expression(E.arg(1), TargetBitwidth);
                if (A1.get_sort().bv_size() == TargetBitwidth && A2.get_sort().bv_size() == TargetBitwidth) {
                    return Z3::sub(A1, A2);
                }
            }
                break;
            case Z3_OP_BMUL: {
                assert(E.num_args() == 2);
                auto A1 = Z3::trunc_expression(E.arg(0), TargetBitwidth);
                auto A2 = Z3::trunc_expression(E.arg(1), TargetBitwidth);
                if (A1.get_sort().bv_size() == TargetBitwidth && A2.get_sort().bv_size() == TargetBitwidth) {
                    return Z3::mul(A1, A2);
                }
            }
                break;
            case Z3_OP_BSDIV_I:
            case Z3_OP_BSDIV:
            case Z3_OP_BUDIV_I:
            case Z3_OP_BUDIV:
            case Z3_OP_BSMOD:
            case Z3_OP_BSMOD_I:
            case Z3_OP_BSREM:
            case Z3_OP_BSREM_I:
            case Z3_OP_BUREM:
            case Z3_OP_BUREM_I:
            case Z3_OP_BAND:
            case Z3_OP_BOR:
            case Z3_OP_BNOT:
            case Z3_OP_BXOR:
            case Z3_OP_BNAND:
            case Z3_OP_BNOR:
            case Z3_OP_BXNOR:
            case Z3_OP_BSHL:
            case Z3_OP_BLSHR:
            case Z3_OP_BASHR:
            default: {
                if (DeclKind == Z3_OP_CONCAT) {
                    auto Head = E.arg(0);
                    uint64_t Zero;
                    if (Z3::is_numeral_u64(Head, Zero) && Zero == 0 && Head.get_sort().bv_size() >= TruncSize) {
                        return Z3::trunc(E, TargetBitwidth);
                    }
                } else if (DeclKind == Z3_OP_BNUM) {
                    uint64_t Num;
                    if (Z3::is_numeral_u64(E, Num) && Num == ((Num << TruncSize) >> TruncSize)) {
                        return Z3::trunc(E, TargetBitwidth);
                    }
                } else if (is_base(E)) {
                    return Z3::trunc(E, TargetBitwidth);
                }
            }
        }
    }
    return E;
}

z3::expr Z3::zext(const z3::expr &E, unsigned TargetBitwidth) {
    assert(E.is_bv());
    assert(E.get_sort().bv_size() <= TargetBitwidth);
    if (E.get_sort().bv_size() == TargetBitwidth) return E;
    if (Z3::is_free(E)) return Z3::free_bv(TargetBitwidth);

    uint64_t Const;
    if (E.decl().decl_kind() == Z3_OP_ITE) {
        return z3::ite(E.arg(0),
                       Z3::zext(E.arg(1), TargetBitwidth),
                       Z3::zext(E.arg(2), TargetBitwidth));
    } else if (is_phi(E)) {
        auto RetVec = Z3::vec();
        for (unsigned I = 0; I < E.num_args(); ++I) {
            RetVec.push_back(zext(E.arg(I), TargetBitwidth));
        }
        return Z3::make_phi(Z3::phi_id(E), RetVec);
    } else if (Z3::is_numeral_u64(E, Const)) {
        return Z3::bv_val(Const, TargetBitwidth);
    } else {
        return z3::zext(E, TargetBitwidth - E.get_sort().bv_size());
    }
}

z3::expr Z3::sext(const z3::expr &E, unsigned TargetBitwidth) {
    assert(E.is_bv());
    assert(E.get_sort().bv_size() <= TargetBitwidth);
    if (E.get_sort().bv_size() == TargetBitwidth) return E;
    if (Z3::is_free(E)) return Z3::free_bv(TargetBitwidth);

    int64_t Const;
    if (E.decl().decl_kind() == Z3_OP_ITE) {
        return z3::ite(E.arg(0),
                       Z3::sext(E.arg(1), TargetBitwidth),
                       Z3::sext(E.arg(2), TargetBitwidth));
    } else if (is_phi(E)) {
        auto RetVec = Z3::vec();
        for (unsigned I = 0; I < E.num_args(); ++I) {
            RetVec.push_back(sext(E.arg(I), TargetBitwidth));
        }
        return Z3::make_phi(Z3::phi_id(E), RetVec);
    } else if (Z3::is_numeral_i64(E, Const)) {
        return Z3::bv_val(Const, TargetBitwidth);
    } else {
        return z3::sext(E, TargetBitwidth - E.get_sort().bv_size());
    }
}

z3::expr Z3::bv_to_bool(const z3::expr &E) {
    return Z3::ne(bv_val(0, E.get_sort().bv_size()), E);
}

z3::expr Z3::bool_to_bv(const z3::expr &C, unsigned Sz) {
    assert(C.is_bool());
    if (C.is_true())
        return Z3::bv_val(1, Sz);
    else if (C.is_false())
        return Z3::bv_val(0, Sz);
    else if (Z3::is_free(C))
        return Z3::free_bv(Sz);
    else if (C.decl().decl_kind() == Z3_OP_ITE) {
        return Z3::ite(C.arg(0), bool_to_bv(C.arg(1), Sz), bool_to_bv(C.arg(2), Sz));
    } else if (is_phi(C)) {
        auto ResultVec = Z3::vec();
        for (unsigned I = 0; I < C.num_args(); ++I) {
            ResultVec.push_back(bool_to_bv(C.arg(I), Sz));
        }
        return Z3::make_phi(Z3::phi_id(C), ResultVec);
    }
    return Z3::ite(C, Z3::bv_val(1, Sz), Z3::bv_val(0, Sz));
}