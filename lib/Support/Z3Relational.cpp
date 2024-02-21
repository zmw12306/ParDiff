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

static inline z3::expr eq_zero(const z3::expr &O) {
    if (Z3::is_free(O)) return Z3::free_bool();
    if (O.decl().decl_kind() == Z3_OP_ITE) {
        uint64_t Zero;
        bool Arg1Const = O.arg(1).is_numeral_u64(Zero);
        bool Arg1Zero = Arg1Const && Zero == 0;
        bool Arg2Const = O.arg(2).is_numeral_u64(Zero);
        bool Arg2Zero = Arg2Const && Zero == 0;
        if (Arg1Const && Arg2Const) {
            if (Arg1Zero && Arg2Zero) {
                return Z3::bool_val(true);
            } else if (Arg1Zero) {
                return O.arg(0);
            } else if (Arg2Zero) {
                return Z3::negation(O.arg(0));
            } else {
                return Z3::bool_val(false);
            }
        } else if (Arg1Const && !Arg1Zero) {
            return Z3::make_and(Z3::negation(O.arg(0)), eq_zero(O.arg(2)));
        } else if (Arg2Const && !Arg2Zero) {
            return Z3::make_and(O.arg(0), eq_zero(O.arg(1)));
        }
    } else if (O.decl().decl_kind() == Z3_OP_BOR) {
        auto OpVec = Z3::find_consecutive_ops(O, Z3_OP_BOR);
        std::vector<z3::expr> Vec;
        for (auto Op: OpVec) {
            Vec.push_back(eq_zero(Op));
        }
        return Z3::make_and(Vec);
    } else if (O.decl().decl_kind() == Z3_OP_BXOR) {
        auto A1 = O.arg(0);
        auto A2 = O.arg(1);
        if (A1.decl().decl_kind() == Z3_OP_ITE && A2.decl().decl_kind() == Z3_OP_ITE) {
            if (Z3::same(A1.arg(1), A2.arg(1)) && Z3::same(A1.arg(2), A2.arg(2))) {
                // (a1 ? x : y ^ a2 ? x : y) = 0 => a1 == a2
                return (A1.arg(0) == A2.arg(0)).simplify();
            } else if (Z3::same(A1.arg(1), A2.arg(2)) && Z3::same(A1.arg(2), A2.arg(1))) {
                return (A1.arg(0) != A2.arg(0)).simplify();
            }
        }
    }
    return (O == 0).simplify();
}

static inline z3::expr ne_zero(const z3::expr &O) {
    if (Z3::is_free(O)) return Z3::free_bool();
    if (O.decl().decl_kind() == Z3_OP_ITE) {
        uint64_t Zero;
        bool Arg1Const = O.arg(1).is_numeral_u64(Zero);
        bool Arg1Zero = Arg1Const && Zero == 0;
        bool Arg2Const = O.arg(2).is_numeral_u64(Zero);
        bool Arg2Zero = Arg2Const && Zero == 0;
        if (Arg1Const && Arg2Const) {
            if (Arg1Zero && Arg2Zero) {
                return Z3::bool_val(false);
            } else if (Arg1Zero) {
                return Z3::negation(O.arg(0));
            } else if (Arg2Zero) {
                return O.arg(0);
            } else {
                return Z3::bool_val(true);
            }
        } else if (Arg1Const && Arg1Zero) {
            return Z3::make_and(Z3::negation(O.arg(0)), ne_zero(O.arg(2)));
        } else if (Arg2Const && Arg2Zero) {
            return Z3::make_and(O.arg(0), ne_zero(O.arg(1)));
        }
    } else if (O.decl().decl_kind() == Z3_OP_BXOR) {
        auto A1 = O.arg(0);
        auto A2 = O.arg(1);
        if (A1.decl().decl_kind() == Z3_OP_ITE && A2.decl().decl_kind() == Z3_OP_ITE) {
            if (Z3::same(A1.arg(1), A2.arg(1)) && Z3::same(A1.arg(2), A2.arg(2))) {
                // (a1 ? x : y ^ a2 ? x : y) != 0 => a1 != a2
                return (A1.arg(0) != A2.arg(0)).simplify();
            } else if (Z3::same(A1.arg(1), A2.arg(2)) && Z3::same(A1.arg(2), A2.arg(1))) {
                return (A1.arg(0) == A2.arg(0)).simplify();
            }
        }
    }
    return (O != 0).simplify();
}

template<class ExprCompare>
static inline z3::expr compare_with_one_of(const z3::expr &O1, const z3::expr &O2, ExprCompare EC) {
    if (Z3::is_free(O1) || Z3::is_free(O2)) return Z3::free_bool();

    if (Z3::is_phi(O1) && !Z3::is_phi(O2)) {
        auto Vec = Z3::vec();
        for (unsigned I = 0; I < O1.num_args(); ++I) {
            Vec.push_back(compare_with_one_of(O1.arg(I), O2, EC));
        }
        return Z3::make_phi(Z3::phi_id(O1), Vec);
    } else if (!Z3::is_phi(O1) && Z3::is_phi(O2)) {
        auto Vec = Z3::vec();
        for (unsigned I = 0; I < O2.num_args(); ++I) {
            Vec.push_back(compare_with_one_of(O1, O2.arg(I), EC));
        }
        return Z3::make_phi(Z3::phi_id(O2), Vec);
    } else if (Z3::same_phi(O1, O2)) {
        auto Vec = Z3::vec();
        for (unsigned I = 0; I < O2.num_args(); ++I) {
            Vec.push_back(compare_with_one_of(O1.arg(I), O2.arg(I), EC));
        }
        return Z3::make_phi(Z3::phi_id(O1), Vec);
    } else if (O1.decl().decl_kind() == Z3_OP_ITE && O2.decl().decl_kind() != Z3_OP_ITE) {
        auto Res1 = compare_with_one_of(O1.arg(1), O2, EC);
        auto Res2 = compare_with_one_of(O1.arg(2), O2, EC);
        if (Res1.is_true() && Res2.is_false()) {
            return O1.arg(0);
        } else if (Res1.is_false() && Res2.is_true()) {
            return Z3::negation(O1.arg(0));
        } else if (Res1.is_false() && Res2.is_false()) {
            return Z3::bool_val(false);
        } else if (Res1.is_true() && Res2.is_true()) {
            return Z3::bool_val(true);
        }
    } else if (O1.decl().decl_kind() != Z3_OP_ITE && O2.decl().decl_kind() == Z3_OP_ITE) {
        auto Res1 = compare_with_one_of(O1, O2.arg(1), EC);
        auto Res2 = compare_with_one_of(O1, O2.arg(2), EC);
        if (Res1.is_true() && Res2.is_false()) {
            return O2.arg(0);
        } else if (Res1.is_false() && Res2.is_true()) {
            return Z3::negation(O2.arg(0));
        } else if (Res1.is_false() && Res2.is_false()) {
            return Z3::bool_val(false);
        } else if (Res1.is_true() && Res2.is_true()) {
            return Z3::bool_val(true);
        }
    } else if (O1.decl().decl_kind() == Z3_OP_BADD && O2.decl().decl_kind() == Z3_OP_BADD) {
        // do some aggressive rewriting by eliminating the same items between a relational operator
        //  e.g., -8 + len < -10 + len => -8 < -10, assuming no overflow/underflow
        auto O1Ops = Z3::find_consecutive_ops(O1, Z3_OP_BADD, true);
        auto O2Ops = Z3::find_consecutive_ops(O2, Z3_OP_BADD, true);
        bool Changed = false;
        for (unsigned I = 0; I < O1Ops.size(); ++I) {
            auto E1 = O1Ops[I];
            bool FoundSame = false;
            for (unsigned J = 0; J < O2Ops.size(); ++J) {
                auto E2 = O2Ops[J];
                if (Z3::same(E1, E2)) {
                    // remove E2 from O2Ops
                    auto Back2 = O2Ops.back();
                    O2Ops.set(J, Back2);
                    O2Ops.pop_back();
                    FoundSame = true;
                    if (!Changed) Changed = true;
                    break;
                }
            }
            if (FoundSame) {
                // remove E1 from O1Ops
                auto Back1 = O1Ops.back();
                O1Ops.set(I, Back1);
                O1Ops.pop_back();
                I--;
            }
        }
        if (Changed) {
            // xx < xx - 10 => 0 < -10 => 10 < 0; otherwise unsigned ops will make mistakes.
            auto MoveNegativeItem = [](z3::expr_vector &O1Ops, z3::expr_vector &O2Ops) {
                for (unsigned I = 0; I < O1Ops.size(); ++I) {
                    auto E = O1Ops[I];
                    int64_t Const;
                    if (E.decl().decl_kind() == Z3_OP_BMUL) {
                        assert(E.num_args() == 2);
                        int64_t Const;
                        if (Z3::is_numeral_i64(E.arg(0), Const) && Const < 0) {
                            auto Back = O1Ops.back();
                            O1Ops.set(I--, Back);
                            O1Ops.pop_back();
                            O2Ops.push_back(Const == -1 ? E.arg(1) : ((int) -Const) * E.arg(1));
                        } else if (Z3::is_numeral_i64(E.arg(1), Const) && Const < 0) {
                            auto Back = O1Ops.back();
                            O1Ops.set(I--, Back);
                            O1Ops.pop_back();
                            O2Ops.push_back(Const == -1 ? E.arg(0) : ((int) -Const) * E.arg(0));
                        }
                    } else if (Z3::is_numeral_i64(E, Const)) {
                        if (Const == 0) {
                            auto Back = O1Ops.back();
                            O1Ops.set(I--, Back);
                            O1Ops.pop_back();
                        } else if (Const < 0) {
                            auto Back = O1Ops.back();
                            O1Ops.set(I--, Back);
                            O1Ops.pop_back();
                            O2Ops.push_back(Z3::bv_val(-Const, E.get_sort().bv_size()));
                        }
                    }
                }
            };
            MoveNegativeItem(O1Ops, O2Ops);
            MoveNegativeItem(O2Ops, O1Ops);

            auto BvSum = [](const z3::expr_vector &V) {
                // note: z3::sum() does not support bit vector
                assert(V.size() > 0);
                auto Ret = V[0];
                for (unsigned K = 1; K < V.size(); ++K) {
                    Ret = Ret + V[K];
                }
                return Ret.simplify();
            };

            auto BvSz = O1.get_sort().bv_size();
            z3::expr NewO1 = O1Ops.empty() ? Z3::bv_val(0, BvSz) : BvSum(O1Ops);
            z3::expr NewO2 = O2Ops.empty() ? Z3::bv_val(0, BvSz) : BvSum(O2Ops);
            return compare_with_one_of(NewO1, NewO2, EC);
        }
    }
    return EC(O1, O2);
}

z3::expr Z3::slt(const z3::expr &O1, const z3::expr &O2) {
    return compare_with_one_of(O1, O2, [](const z3::expr &A, const z3::expr &B) { return (A < B).simplify(); });
}

z3::expr Z3::sle(const z3::expr &O1, const z3::expr &O2) {
    return negation(slt(O2, O1));
}

z3::expr Z3::sgt(const z3::expr &O1, const z3::expr &O2) {
    return slt(O2, O1);
}

z3::expr Z3::sge(const z3::expr &O1, const z3::expr &O2) {
    return negation(slt(O1, O2));
}

static uint64_t get_unsigned_max(const z3::expr &E) {
    if (E.decl().decl_kind() == Z3_OP_CONCAT && E.num_args() == 2) {
        auto Prefix = E.arg(0);
        auto RealExpr = E.arg(1);
        uint64_t Const;
        if (Z3::is_numeral_u64(Prefix, Const) && Const == 0) {
            return get_unsigned_max(RealExpr);
        }
    }

    unsigned EBW = E.get_sort().bv_size();
    if (EBW < 64) {
        uint64_t Ret = 1;
        return (Ret << EBW) - 1;
    } else {
        return UINT64_MAX;
    }
}

z3::expr Z3::ult(const z3::expr &O1, const z3::expr &O2) {
    auto Ret = compare_with_one_of(O1, O2, [](const z3::expr &A, const z3::expr &B) {
        // 255 < B[i] => false
        uint64_t Const;
        if (A.get_sort().bv_size() <= 64 && Z3::is_numeral_u64(A, Const)) {
            uint64_t Max = get_unsigned_max(B);
            if (Max <= Const) {
                return Z3::bool_val(false);
            }
        }
        return z3::ult(A, B).simplify();
    });
    return Ret;
}

z3::expr Z3::ule(const z3::expr &O1, const z3::expr &O2) {
    return negation(ult(O2, O1));
}

z3::expr Z3::ugt(const z3::expr &O1, const z3::expr &O2) {
    return ult(O2, O1);
}

z3::expr Z3::uge(const z3::expr &O1, const z3::expr &O2) {
    return negation(ult(O1, O2));
}

z3::expr Z3::eq(const z3::expr &O1, const z3::expr &O2) {
    return compare_with_one_of(O1, O2, [](const z3::expr &A, const z3::expr &B) {
        uint64_t Const;
        if (Z3::is_numeral_u64(A, Const) && !Const) {
            return eq_zero(B);
        } else if (Z3::is_numeral_u64(B, Const) && !Const) {
            return eq_zero(A);
        }
        return (A == B).simplify();
    });
}

z3::expr Z3::ne(const z3::expr &O1, const z3::expr &O2) {
    return compare_with_one_of(O1, O2, [](const z3::expr &A, const z3::expr &B) {
        uint64_t Const;
        if (Z3::is_numeral_u64(A, Const) && !Const) {
            return ne_zero(B);
        } else if (Z3::is_numeral_u64(B, Const) && !Const) {
            return ne_zero(A);
        }
        return (A != B).simplify();
    });
}

bool Z3::is_compare(const z3::expr &E) {
    switch (E.decl().decl_kind()) {
        case Z3_OP_SLEQ:
        case Z3_OP_SLT:
        case Z3_OP_SGEQ:
        case Z3_OP_SGT:
        case Z3_OP_ULEQ:
        case Z3_OP_ULT:
        case Z3_OP_UGEQ:
        case Z3_OP_UGT:
        case Z3_OP_EQ:
        case Z3_OP_DISTINCT:
            return true;
        default:
            return false;
    }
}