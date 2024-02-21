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

z3::expr Z3::simplify(const z3::expr_vector &Orig) {
    z3::expr_vector NewVec = Z3::vec();
    for (auto E: Orig) {
        auto Vec = Z3::find_consecutive_ops(E, Z3_OP_AND);
        for (auto V: Vec)
            NewVec.push_back(V);
    }
    DEBUG_WITH_TYPE("Z3Simplify", dbgs() << ">>> Original Exprs:" << "\n");
    DEBUG_WITH_TYPE("Z3Simplify", for (auto E: NewVec) dbgs() << "\t" << E << "\n");
    auto False = Z3::bool_val(false);
    for (int I = 0; I < NewVec.size(); ++I) {
        auto ExprI = NewVec[I];
        bool FalseFound = false;
        for (int J = 0; J < NewVec.size(); ++J) {
            if (I == J) continue;
            auto ExprJ = NewVec[J];
            auto ExprJAfterSimplify = Z3::simplify(ExprI, ExprJ);
            if (ExprJAfterSimplify.is_false()) {
                NewVec.set(J, False);
                FalseFound = true;
                break;
            } else if (!Z3::same(ExprJ, ExprJAfterSimplify)) {
                NewVec.set(J, ExprJAfterSimplify);
            }
        }
        if (FalseFound) break;
    }
    DEBUG_WITH_TYPE("Z3Simplify", dbgs() << ">>> Exprs (1):" << "\n");
    DEBUG_WITH_TYPE("Z3Simplify", for (auto E: NewVec) dbgs() << "\t" << E << "\n");

    auto AndExpr = Z3::make_and(NewVec);
    AndExpr = AndExpr.simplify();
    if (!AndExpr.is_and()) {
        return AndExpr;
    }
    NewVec.resize(0);
    for (unsigned I = 0; I < AndExpr.num_args(); ++I) {
        NewVec.push_back(AndExpr.arg(I).simplify());
    }
    DEBUG_WITH_TYPE("Z3Simplify", dbgs() << ">>> Exprs (2):" << "\n");
    DEBUG_WITH_TYPE("Z3Simplify", for (auto E: NewVec) dbgs() << "\t" << E << "\n");

    while (true) {
        bool Changed = false;
        for (int I = 0; I < NewVec.size(); ++I) {
            auto Arg = NewVec[I];
            z3::expr_vector From = Z3::vec();
            z3::expr_vector To = Z3::vec();
            if (Arg.is_eq()) {
                From.push_back(Arg);
                To.push_back(Z3::bool_val(true));
                auto Eq1 = Arg.arg(0);
                auto Eq2 = Arg.arg(1);
                uint64_t X;
                if (Z3::is_numeral_u64(Eq1, X)) {
                    From.push_back(Eq2);
                    To.push_back(Eq1);
                } else if (Z3::is_numeral_u64(Eq2, X)) {
                    From.push_back(Eq1);
                    To.push_back(Eq2);
                }
            } else if (Arg.is_not() && Arg.arg(0).is_eq()) {
                From.push_back(Arg.arg(0));
                To.push_back(Z3::bool_val(false));
            }
            if (From.empty()) continue;
            for (int J = 0; J < NewVec.size(); ++J) {
                if (I == J) continue;
                auto ExprJ = NewVec[J];
                if (Z3::is_naming_eq(ExprJ)) continue;
                auto ExprJAfterSimplify = ExprJ.substitute(From, To).simplify();
                if (!Z3::same(ExprJAfterSimplify, ExprJ)) {
                    NewVec.set(J, ExprJAfterSimplify);
                    if (!Changed) Changed = true;
                }
            }
        }
        if (!Changed) break;
    }
    DEBUG_WITH_TYPE("Z3Simplify", dbgs() << ">>> Exprs (3):" << "\n");
    DEBUG_WITH_TYPE("Z3Simplify", for (auto E: NewVec) dbgs() << "\t" << E << "\n");

    auto Ret = Z3::make_and(NewVec).simplify();
    DEBUG_WITH_TYPE("Z3Simplify", dbgs() << ">>> Exprs (4):" << "\n");
    DEBUG_WITH_TYPE("Z3Simplify", dbgs() << "\t" << Ret << "\n----------\n");
    return Ret;
}

static inline z3::expr normalize(const z3::expr &E) {
    if (E.is_not()) {
        auto Arg = E.arg(0);
        if (Arg.num_args() != 2)
            return E;

        uint64_t X;
        auto Arg0 = Arg.arg(0);
        auto Arg1 = Arg.arg(1);
        auto Arg0Const = Z3::is_numeral_u64(Arg0, X);
        (void) X;

        switch (Arg.decl().decl_kind()) {
            case Z3_OP_EQ:
                return Arg0Const ? Arg1 != Arg0 : Arg0 != Arg1;
            case Z3_OP_DISTINCT:
                return Arg0Const ? Arg1 == Arg0 : Arg0 == Arg1;
            case Z3_OP_UGT:
                return Arg0Const ? z3::uge(Arg1, Arg0) : z3::ule(Arg0, Arg1);
            case Z3_OP_ULT:
                return Arg0Const ? z3::ule(Arg1, Arg0) : z3::uge(Arg0, Arg1);
            case Z3_OP_UGEQ:
                return Arg0Const ? z3::ugt(Arg1, Arg0) : z3::ult(Arg0, Arg1);
            case Z3_OP_ULEQ:
                return Arg0Const ? z3::ult(Arg1, Arg0) : z3::ugt(Arg0, Arg1);
            case Z3_OP_SGT:
                return Arg0Const ? z3::sge(Arg1, Arg0) : z3::sle(Arg0, Arg1);
            case Z3_OP_SLT:
                return Arg0Const ? z3::sle(Arg1, Arg0) : z3::sge(Arg0, Arg1);
            case Z3_OP_SGEQ:
                return Arg0Const ? z3::sgt(Arg1, Arg0) : z3::slt(Arg0, Arg1);
            case Z3_OP_SLEQ:
                return Arg0Const ? z3::slt(Arg1, Arg0) : z3::sgt(Arg0, Arg1);
            default:
                break;
        }
    } else if (E.num_args() == 2) {
        uint64_t X;
        auto Arg0 = E.arg(0);
        auto Arg1 = E.arg(1);
        auto Arg0Const = Z3::is_numeral_u64(Arg0, X);
        (void) X;

        switch (E.decl().decl_kind()) {
            case Z3_OP_EQ:
                return Arg0Const ? Arg1 == Arg0 : Arg0 == Arg1;
            case Z3_OP_DISTINCT:
                return Arg0Const ? Arg1 != Arg0 : Arg0 != Arg1;
            case Z3_OP_UGT:
                return Arg0Const ? z3::ult(Arg1, Arg0) : z3::ugt(Arg0, Arg1);
            case Z3_OP_ULT:
                return Arg0Const ? z3::ugt(Arg1, Arg0) : z3::ult(Arg0, Arg1);
            case Z3_OP_UGEQ:
                return Arg0Const ? z3::ule(Arg1, Arg0) : z3::uge(Arg0, Arg1);
            case Z3_OP_ULEQ:
                return Arg0Const ? z3::uge(Arg1, Arg0) : z3::ule(Arg0, Arg1);
            case Z3_OP_SGT:
                return Arg0Const ? z3::slt(Arg1, Arg0) : z3::sgt(Arg0, Arg1);
            case Z3_OP_SLT:
                return Arg0Const ? z3::sgt(Arg1, Arg0) : z3::slt(Arg0, Arg1);
            case Z3_OP_SGEQ:
                return Arg0Const ? z3::sle(Arg1, Arg0) : z3::sge(Arg0, Arg1);
            case Z3_OP_SLEQ:
                return Arg0Const ? z3::sge(Arg1, Arg0) : z3::sle(Arg0, Arg1);
            default:
                break;
        }
    }
    return E;
}

static inline z3::expr simplify_eq_eq(const z3::expr &EQ1, const z3::expr &EQ2) {
    // a = 1 & a = 2 => false
    // a = 1 & a = 1 => true
    auto E1A1 = EQ1.arg(0);
    auto E1A2 = EQ1.arg(1);
    auto E2A1 = EQ2.arg(0);
    auto E2A2 = EQ2.arg(1);
    if (Z3::same(E1A1, E2A2)) {
        E2A1 = EQ2.arg(1);
        E2A2 = EQ2.arg(0);
    } else if (Z3::same(E1A2, E2A1)) {
        E1A1 = EQ1.arg(1);
        E1A2 = EQ1.arg(0);
    } else if (Z3::same(E1A2, E2A2)) {
        E1A1 = EQ1.arg(1);
        E1A2 = EQ1.arg(0);
        E2A1 = EQ2.arg(1);
        E2A2 = EQ2.arg(0);
    }

    if (Z3::same(E1A1, E2A1)) {
        uint64_t C1, C2;
        if (Z3::is_numeral_u64(E1A2, C1) && Z3::is_numeral_u64(E2A2, C2)) {
            return C1 == C2 ? Z3::bool_val(true) : Z3::bool_val(false);
        }
    }
    return EQ2;
}

static inline z3::expr simplify_eq_ne(const z3::expr &EQ1, const z3::expr &NE2) {
    // a = 1 & a != 2 => true
    // a = x & a !=(><) x => false
    auto E1A1 = EQ1.arg(0);
    auto E1A2 = EQ1.arg(1);
    auto E2A1 = NE2.arg(0);
    auto E2A2 = NE2.arg(1);
    if (Z3::same(E1A1, E2A2)) {
        E2A1 = NE2.arg(1);
        E2A2 = NE2.arg(0);
    } else if (Z3::same(E1A2, E2A1)) {
        E1A1 = EQ1.arg(1);
        E1A2 = EQ1.arg(0);
    } else if (Z3::same(E1A2, E2A2)) {
        E1A1 = EQ1.arg(1);
        E1A2 = EQ1.arg(0);
        E2A1 = NE2.arg(1);
        E2A2 = NE2.arg(0);
    }

    if (Z3::same(E1A1, E2A1)) {
        if (Z3::same(E1A2, E2A2)) {
            return Z3::bool_val(false);
        }

        uint64_t C1, C2;
        if (Z3::is_numeral_u64(E1A2, C1) && Z3::is_numeral_u64(E2A2, C2)) {
            return C1 == C2 ? Z3::bool_val(false) : Z3::bool_val(true);
        }
    }
    return NE2;
}

static inline z3::expr simplify_eq_ugt(const z3::expr &E1, const z3::expr &E2) {
    auto A1 = E1.arg(0);
    auto A2 = E1.arg(1);
    auto A3 = E2.arg(0);
    auto A4 = E2.arg(1);

    if (Z3::same(A1, A3) && Z3::same(A2, A4)) {
        return Z3::bool_val(false);
    } else if (Z3::same(A1, A3)) {
        // a = X, X > Y |- a > Y => true
        uint64_t X, Y;
        if (Z3::is_numeral_u64(A2, X) && Z3::is_numeral_u64(A4, Y)) {
            if (X > Y) return Z3::bool_val(true);
            else return Z3::bool_val(false);
        }
    }
    return E2;
}

static inline z3::expr simplify_eq_ult(const z3::expr &E1, const z3::expr &E2) {
    auto A1 = E1.arg(0);
    auto A2 = E1.arg(1);
    auto A3 = E2.arg(0);
    auto A4 = E2.arg(1);

    if (Z3::same(A1, A3) && Z3::same(A2, A4)) {
        return Z3::bool_val(false);
    } else if (Z3::same(A1, A3)) {
        // a = X, X < Y |- a < Y => true
        uint64_t X, Y;
        if (Z3::is_numeral_u64(A2, X) && Z3::is_numeral_u64(A4, Y)) {
            if (X < Y) return Z3::bool_val(true);
            else return Z3::bool_val(false);
        }
    }
    return E2;
}

static inline z3::expr simplify_eq_uge(const z3::expr &E1, const z3::expr &E2) {
    auto A1 = E1.arg(0);
    auto A2 = E1.arg(1);
    auto A3 = E2.arg(0);
    auto A4 = E2.arg(1);

    if (Z3::same(A1, A3) && Z3::same(A2, A4)) {
        return Z3::bool_val(false);
    } else if (Z3::same(A1, A3)) {
        // a = X, X >= Y |- a >= Y => true
        uint64_t X, Y;
        if (Z3::is_numeral_u64(A2, X) && Z3::is_numeral_u64(A4, Y)) {
            if (X >= Y) return Z3::bool_val(true);
            else return Z3::bool_val(false);
        }
    }
    return E2;
}

static inline z3::expr simplify_eq_ule(const z3::expr &E1, const z3::expr &E2) {
    auto A1 = E1.arg(0);
    auto A2 = E1.arg(1);
    auto A3 = E2.arg(0);
    auto A4 = E2.arg(1);

    if (Z3::same(A1, A3) && Z3::same(A2, A4)) {
        return Z3::bool_val(false);
    } else if (Z3::same(A1, A3)) {
        // a = X, X <= Y |- a <= Y => true
        uint64_t X, Y;
        if (Z3::is_numeral_u64(A2, X) && Z3::is_numeral_u64(A4, Y)) {
            if (X <= Y) return Z3::bool_val(true);
            else return Z3::bool_val(false);
        }
    }
    return E2;
}

static inline z3::expr simplify_eq_sgt(const z3::expr &E1, const z3::expr &E2) {
    auto A1 = E1.arg(0);
    auto A2 = E1.arg(1);
    auto A3 = E2.arg(0);
    auto A4 = E2.arg(1);

    if (Z3::same(A1, A3) && Z3::same(A2, A4)) {
        return Z3::bool_val(false);
    } else if (Z3::same(A1, A3)) {
        // a = X, X > Y |- a > Y => true
        int64_t X, Y;
        if (Z3::is_numeral_i64(A2, X) && Z3::is_numeral_i64(A4, Y)) {
            if (X > Y) return Z3::bool_val(true);
            else return Z3::bool_val(false);
        }
    }
    return E2;
}

static inline z3::expr simplify_eq_slt(const z3::expr &E1, const z3::expr &E2) {
    auto A1 = E1.arg(0);
    auto A2 = E1.arg(1);
    auto A3 = E2.arg(0);
    auto A4 = E2.arg(1);

    if (Z3::same(A1, A3) && Z3::same(A2, A4)) {
        return Z3::bool_val(false);
    } else if (Z3::same(A1, A3)) {
        // a = X, X < Y |- a < Y => true
        int64_t X, Y;
        if (Z3::is_numeral_i64(A2, X) && Z3::is_numeral_i64(A4, Y)) {
            if (X < Y) return Z3::bool_val(true);
            else return Z3::bool_val(false);
        }
    }
    return E2;
}

static inline z3::expr simplify_eq_sge(const z3::expr &E1, const z3::expr &E2) {
    auto A1 = E1.arg(0);
    auto A2 = E1.arg(1);
    auto A3 = E2.arg(0);
    auto A4 = E2.arg(1);

    if (Z3::same(A1, A3) && Z3::same(A2, A4)) {
        return Z3::bool_val(false);
    } else if (Z3::same(A1, A3)) {
        // a = X, X >= Y |- a >= Y => true
        int64_t X, Y;
        if (Z3::is_numeral_i64(A2, X) && Z3::is_numeral_i64(A4, Y)) {
            if (X >= Y) return Z3::bool_val(true);
            else return Z3::bool_val(false);
        }
    }
    return E2;
}

static inline z3::expr simplify_eq_sle(const z3::expr &E1, const z3::expr &E2) {
    auto A1 = E1.arg(0);
    auto A2 = E1.arg(1);
    auto A3 = E2.arg(0);
    auto A4 = E2.arg(1);

    if (Z3::same(A1, A3) && Z3::same(A2, A4)) {
        return Z3::bool_val(false);
    } else if (Z3::same(A1, A3)) {
        // a = X, X <= Y |- a <= Y => true
        int64_t X, Y;
        if (Z3::is_numeral_i64(A2, X) && Z3::is_numeral_i64(A4, Y)) {
            if (X <= Y) return Z3::bool_val(true);
            else return Z3::bool_val(false);
        }
    }
    return E2;
}

static inline z3::expr simplify_ne_eq(const z3::expr &NE, const z3::expr &EQ) {
    // a != x & a = x => false
    auto E1A1 = NE.arg(0);
    auto E1A2 = NE.arg(1);
    auto E2A1 = EQ.arg(0);
    auto E2A2 = EQ.arg(1);
    if (Z3::same(E1A1, E2A2)) {
        E2A1 = EQ.arg(1);
        E2A2 = EQ.arg(0);
    } else if (Z3::same(E1A2, E2A1)) {
        E1A1 = NE.arg(1);
        E1A2 = NE.arg(0);
    } else if (Z3::same(E1A2, E2A2)) {
        E1A1 = NE.arg(1);
        E1A2 = NE.arg(0);
        E2A1 = EQ.arg(1);
        E2A2 = EQ.arg(0);
    }

    if (Z3::same(E1A1, E2A1) && Z3::same(E1A2, E2A2)) {
        return Z3::bool_val(false);
    }
    return EQ;
}

static inline z3::expr simplify_ne_ne(const z3::expr &E1, const z3::expr &E2) {
    auto A1 = E1.arg(0);
    auto A2 = E1.arg(1);
    auto A3 = E2.arg(0);
    auto A4 = E2.arg(1);
    if (Z3::same(A1, A3) && Z3::same(A2, A4))
        return Z3::bool_val(true);
    return E2;
}

static inline z3::expr simplify_ne_ugt(const z3::expr &E1, const z3::expr &E2) {
    return E2;
}

static inline z3::expr simplify_ne_ult(const z3::expr &E1, const z3::expr &E2) {
    return E2;
}

static inline z3::expr simplify_ne_sgt(const z3::expr &E1, const z3::expr &E2) {
    return E2;
}

static inline z3::expr simplify_ne_slt(const z3::expr &E1, const z3::expr &E2) {
    return E2;
}

static inline z3::expr simplify_ne_uge(const z3::expr &E1, const z3::expr &E2) {
    auto A1 = E1.arg(0);
    auto A2 = E1.arg(1);
    auto A3 = E2.arg(0);
    auto A4 = E2.arg(1);
    if (Z3::same(A1, A3) && Z3::same(A2, A4))
        return z3::ugt(A3, A4);
    return E2;
}

static inline z3::expr simplify_ne_ule(const z3::expr &E1, const z3::expr &E2) {
    auto A1 = E1.arg(0);
    auto A2 = E1.arg(1);
    auto A3 = E2.arg(0);
    auto A4 = E2.arg(1);
    if (Z3::same(A1, A3) && Z3::same(A2, A4))
        return z3::ult(A3, A4);
    return E2;
}

static inline z3::expr simplify_ne_sle(const z3::expr &E1, const z3::expr &E2) {
    auto A1 = E1.arg(0);
    auto A2 = E1.arg(1);
    auto A3 = E2.arg(0);
    auto A4 = E2.arg(1);
    if (Z3::same(A1, A3) && Z3::same(A2, A4))
        return z3::slt(A3, A4);
    return E2;
}

static inline z3::expr simplify_ne_sge(const z3::expr &E1, const z3::expr &E2) {
    auto A1 = E1.arg(0);
    auto A2 = E1.arg(1);
    auto A3 = E2.arg(0);
    auto A4 = E2.arg(1);
    if (Z3::same(A1, A3) && Z3::same(A2, A4))
        return z3::sgt(A3, A4);
    return E2;
}

#define SIMPLIFY(INT_TYPE, INT_FUNC, CONDITION, RESULT) { \
    auto A1 = E1.arg(0), A2 = E1.arg(1);\
    auto A3 = E2.arg(0), A4 = E2.arg(1);\
    if (Z3::same(A1, A3)) {\
        INT_TYPE X, Y;\
        if (Z3::is_numeral_##INT_FUNC(A2, X) && Z3::is_numeral_##INT_FUNC(A4, Y)) {\
            if (CONDITION) return Z3::bool_val(RESULT);\
        }\
    }\
    return E2;\
}

#define SIMPLIFY_2(INT_TYPE, INT_FUNC, CONDITION, RESULT) { \
    auto A1 = E1.arg(0), A2 = E1.arg(1);\
    auto A3 = E2.arg(0), A4 = E2.arg(1);\
    if (Z3::same(A1, A3)) {                                \
        if (Z3::same(A2, A4)) return A1 == A3;  \
        INT_TYPE X, Y;\
        if (Z3::is_numeral_##INT_FUNC(A2, X) && Z3::is_numeral_##INT_FUNC(A4, Y)) {\
            if (CONDITION) return Z3::bool_val(RESULT);\
        }\
    }\
    return E2;\
}

// a > x; a = y; x >= y => false;
static inline z3::expr simplify_ugt_eq(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(uint64_t, u64, X >= Y, false)

// a > x; a != y; x >= y => true;
static inline z3::expr simplify_ugt_ne(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(uint64_t, u64, X >= Y, true)

// a > x; a > y; x >= y => true;
static inline z3::expr simplify_ugt_ugt(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(uint64_t, u64, X >= Y, true)

// a > x; a >= y; x >= y => true;
static inline z3::expr simplify_ugt_uge(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(uint64_t, u64, X >= Y, true)

// a > x; a < y; x >= y => false;
static inline z3::expr simplify_ugt_ult(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(uint64_t, u64, X >= Y, false)

// a > x; a <= y; x >= y => false;
static inline z3::expr simplify_ugt_ule(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(uint64_t, u64, X >= Y, false)

static inline z3::expr simplify_ugt_sgt(const z3::expr &E1, const z3::expr &E2) { return E2; }

static inline z3::expr simplify_ugt_slt(const z3::expr &E1, const z3::expr &E2) { return E2; }

static inline z3::expr simplify_ugt_sle(const z3::expr &E1, const z3::expr &E2) { return E2; }

static inline z3::expr simplify_ugt_sge(const z3::expr &E1, const z3::expr &E2) { return E2; }

// a >= x; a == y; x > y => false;
static inline z3::expr simplify_uge_eq(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(uint64_t, u64, X > Y, false)

// a >= x; a != y; x > y => true;
static inline z3::expr simplify_uge_ne(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(uint64_t, u64, X > Y, true)

// a >= x; a > y; x > y => true;
static inline z3::expr simplify_uge_ugt(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(uint64_t, u64, X > Y, true)

// a >= x; a >= y; x >= y => true;
static inline z3::expr simplify_uge_uge(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(uint64_t, u64, X >= Y, true)

// a >= x; a < y; x >= y => false;
static inline z3::expr simplify_uge_ult(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(uint64_t, u64, X >= Y, false)

// a >= x; a <= y; x == y => a == y | x > y => false
static inline z3::expr simplify_uge_ule(const z3::expr &E1, const z3::expr &E2) SIMPLIFY_2(uint64_t, u64, X > Y, false)

static inline z3::expr simplify_uge_sgt(const z3::expr &E1, const z3::expr &E2) { return E2; }

static inline z3::expr simplify_uge_slt(const z3::expr &E1, const z3::expr &E2) { return E2; }

static inline z3::expr simplify_uge_sle(const z3::expr &E1, const z3::expr &E2) { return E2; }

static inline z3::expr simplify_uge_sge(const z3::expr &E1, const z3::expr &E2) { return E2; }

static inline z3::expr simplify_sge_ugt(const z3::expr &E1, const z3::expr &E2) { return E2; }

static inline z3::expr simplify_sge_uge(const z3::expr &E1, const z3::expr &E2) { return E2; }

static inline z3::expr simplify_sge_ult(const z3::expr &E1, const z3::expr &E2) { return E2; }

static inline z3::expr simplify_sge_ule(const z3::expr &E1, const z3::expr &E2) { return E2; }

// a >= x; a == y; x > y => false;
static inline z3::expr simplify_sge_eq(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(int64_t, i64, X > Y, false)

// a >= x; a != y; x > y => true;
static inline z3::expr simplify_sge_ne(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(int64_t, i64, X > Y, true)

// a >= x; a > y; x > y => true;
static inline z3::expr simplify_sge_sgt(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(int64_t, i64, X > Y, true)

// a >= x; a < y; x >= y => false;
static inline z3::expr simplify_sge_slt(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(int64_t, i64, X >= Y, false)

// a >= x; a >= y; x >= y => true;
static inline z3::expr simplify_sge_sge(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(int64_t, i64, X >= Y, true)

// a >= x; a <= y; x == y => a == y | x > y => false
static inline z3::expr simplify_sge_sle(const z3::expr &E1, const z3::expr &E2) SIMPLIFY_2(int64_t, i64, X > Y, false)

// a > x; a = y; x >= y => false;
static inline z3::expr simplify_sgt_eq(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(int64_t, i64, X >= Y, false)

// a > x; a != y; x >= y => true;
static inline z3::expr simplify_sgt_ne(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(int64_t, i64, X >= Y, true)

// a > x; a > y; x >= y => true;
static inline z3::expr simplify_sgt_sgt(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(int64_t, i64, X >= Y, true)

// a > x; a >= y; x >= y => true;
static inline z3::expr simplify_sgt_sge(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(int64_t, i64, X >= Y, true)

// a > x; a < y; x >= y => false;
static inline z3::expr simplify_sgt_slt(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(int64_t, i64, X >= Y, false)

// a > x; a <= y; x >= y => false;
static inline z3::expr simplify_sgt_sle(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(int64_t, i64, X >= Y, false)

static inline z3::expr simplify_sgt_ugt(const z3::expr &E1, const z3::expr &E2) { return E2; }

static inline z3::expr simplify_sgt_uge(const z3::expr &E1, const z3::expr &E2) { return E2; }

static inline z3::expr simplify_sgt_ult(const z3::expr &E1, const z3::expr &E2) { return E2; }

static inline z3::expr simplify_sgt_ule(const z3::expr &E1, const z3::expr &E2) { return E2; }

// a < x; a = y; x <= y => false;
static inline z3::expr simplify_ult_eq(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(uint64_t, u64, X <= Y, false)

// a < x; a != y; x <= y => true;
static inline z3::expr simplify_ult_ne(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(uint64_t, u64, X <= Y, true)

// a < x; a > y; x <= y => false;
static inline z3::expr simplify_ult_ugt(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(uint64_t, u64, X <= Y, false)

// a < x; a >= y; x <= y => false;
static inline z3::expr simplify_ult_uge(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(uint64_t, u64, X <= Y, false)

// a < x; a < y; x <= y => true;
static inline z3::expr simplify_ult_ult(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(uint64_t, u64, X <= Y, true)

// a < x; a <= y; x <= y => true;
static inline z3::expr simplify_ult_ule(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(uint64_t, u64, X <= Y, true)

static inline z3::expr simplify_ult_sgt(const z3::expr &E1, const z3::expr &E2) { return E2; }

static inline z3::expr simplify_ult_slt(const z3::expr &E1, const z3::expr &E2) { return E2; }

static inline z3::expr simplify_ult_sle(const z3::expr &E1, const z3::expr &E2) { return E2; }

static inline z3::expr simplify_ult_sge(const z3::expr &E1, const z3::expr &E2) { return E2; }

// a <= x; a = y; x < y => false;
static inline z3::expr simplify_ule_eq(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(uint64_t, u64, X < Y, false)

// a <= x; a != y; x < y => true;
static inline z3::expr simplify_ule_ne(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(uint64_t, u64, X < Y, true)

// a <= x; a > y; x <= y => false;
static inline z3::expr simplify_ule_ugt(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(uint64_t, u64, X <= Y, false)

// a <= x; a < y; x < y => true;
static inline z3::expr simplify_ule_ult(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(uint64_t, u64, X < Y, true)

// a <= x; a <= y; x <= y => true;
static inline z3::expr simplify_ule_ule(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(uint64_t, u64, X <= Y, true)

// a <= x; a >= y; x = y => a = y | x < y => false;
static inline z3::expr simplify_ule_uge(const z3::expr &E1, const z3::expr &E2) SIMPLIFY_2(uint64_t, u64, X < Y, false)

static inline z3::expr simplify_ule_sgt(const z3::expr &E1, const z3::expr &E2) { return E2; }

static inline z3::expr simplify_ule_slt(const z3::expr &E1, const z3::expr &E2) { return E2; }

static inline z3::expr simplify_ule_sle(const z3::expr &E1, const z3::expr &E2) { return E2; }

static inline z3::expr simplify_ule_sge(const z3::expr &E1, const z3::expr &E2) { return E2; }

static inline z3::expr simplify_slt_ugt(const z3::expr &E1, const z3::expr &E2) { return E2; }

static inline z3::expr simplify_slt_uge(const z3::expr &E1, const z3::expr &E2) { return E2; }

static inline z3::expr simplify_slt_ult(const z3::expr &E1, const z3::expr &E2) { return E2; }

static inline z3::expr simplify_slt_ule(const z3::expr &E1, const z3::expr &E2) { return E2; }

// a < x; a = y; x <= y => false;
static inline z3::expr simplify_slt_eq(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(int64_t, i64, X <= Y, false)

// a < x; a != y; x <= y => true;
static inline z3::expr simplify_slt_ne(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(int64_t, i64, X <= Y, true)

// a < x; a > y; x <= y => false;
static inline z3::expr simplify_slt_sgt(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(int64_t, i64, X <= Y, false)

// a < x; a >= y; x <= y => false;
static inline z3::expr simplify_slt_sge(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(int64_t, i64, X <= Y, false)

// a < x; a < y; x <= y => true;
static inline z3::expr simplify_slt_slt(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(int64_t, i64, X <= Y, true)

// a < x; a <= y; x <= y => true;
static inline z3::expr simplify_slt_sle(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(int64_t, i64, X <= Y, true)

// a <= x; a = y; x < y => false;
static inline z3::expr simplify_sle_eq(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(int64_t, i64, X < Y, false)

// a <= x; a != y; x < y => true;
static inline z3::expr simplify_sle_ne(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(int64_t, i64, X < Y, true)

// a <= x; a > y; x <= y => false;
static inline z3::expr simplify_sle_sgt(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(int64_t, i64, X <= Y, false)

// a <= x; a < y; x < y => true;
static inline z3::expr simplify_sle_slt(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(int64_t, i64, X < Y, true)

// a <= x; a <= y; x <= y => true;
static inline z3::expr simplify_sle_sle(const z3::expr &E1, const z3::expr &E2) SIMPLIFY(int64_t, i64, X <= Y, true)

// a <= x; a >= y; x = y => a = y | x < y => false;
static inline z3::expr simplify_sle_sge(const z3::expr &E1, const z3::expr &E2) SIMPLIFY_2(int64_t, i64, X < Y, false)

static inline z3::expr simplify_sle_ugt(const z3::expr &E1, const z3::expr &E2) { return E2; }

static inline z3::expr simplify_sle_uge(const z3::expr &E1, const z3::expr &E2) { return E2; }

static inline z3::expr simplify_sle_ult(const z3::expr &E1, const z3::expr &E2) { return E2; }

static inline z3::expr simplify_sle_ule(const z3::expr &E1, const z3::expr &E2) { return E2; }

static inline z3::expr simplify_eq(const z3::expr &E1, const z3::expr &E2) {
    switch (E2.decl().decl_kind()) {
        case Z3_OP_EQ:
            return simplify_eq_eq(E1, E2);
        case Z3_OP_DISTINCT:
            return simplify_eq_ne(E1, E2);
        case Z3_OP_UGT:
            return simplify_eq_ugt(E1, E2);
        case Z3_OP_ULT:
            return simplify_eq_ult(E1, E2);
        case Z3_OP_SGT:
            return simplify_eq_sgt(E1, E2);
        case Z3_OP_SLT:
            return simplify_eq_slt(E1, E2);
        case Z3_OP_UGEQ:
            return simplify_eq_uge(E1, E2);
        case Z3_OP_ULEQ:
            return simplify_eq_ule(E1, E2);
        case Z3_OP_SGEQ:
            return simplify_eq_sge(E1, E2);
        case Z3_OP_SLEQ:
            return simplify_eq_sle(E1, E2);
        default:
            break;
    }
    return E2;
}

static inline z3::expr simplify_ne(const z3::expr &E1, const z3::expr &E2) {
    switch (E2.decl().decl_kind()) {
        case Z3_OP_EQ:
            return simplify_ne_eq(E1, E2);
        case Z3_OP_DISTINCT:
            return simplify_ne_ne(E1, E2);
        case Z3_OP_UGT:
            return simplify_ne_ugt(E1, E2);
        case Z3_OP_ULT:
            return simplify_ne_ult(E1, E2);
        case Z3_OP_SGT:
            return simplify_ne_sgt(E1, E2);
        case Z3_OP_SLT:
            return simplify_ne_slt(E1, E2);
        case Z3_OP_UGEQ:
            return simplify_ne_uge(E1, E2);
        case Z3_OP_ULEQ:
            return simplify_ne_ule(E1, E2);
        case Z3_OP_SGEQ:
            return simplify_ne_sge(E1, E2);
        case Z3_OP_SLEQ:
            return simplify_ne_sle(E1, E2);
        default:
            break;
    }
    return E2;
}

static inline z3::expr simplify_ugt(const z3::expr &E1, const z3::expr &E2) {
    switch (E2.decl().decl_kind()) {
        case Z3_OP_EQ:
            return simplify_ugt_eq(E1, E2);
        case Z3_OP_DISTINCT:
            return simplify_ugt_ne(E1, E2);
        case Z3_OP_UGT:
            return simplify_ugt_ugt(E1, E2);
        case Z3_OP_ULT:
            return simplify_ugt_ult(E1, E2);
        case Z3_OP_SGT:
            return simplify_ugt_sgt(E1, E2);
        case Z3_OP_SLT:
            return simplify_ugt_slt(E1, E2);
        case Z3_OP_UGEQ:
            return simplify_ugt_uge(E1, E2);
        case Z3_OP_ULEQ:
            return simplify_ugt_ule(E1, E2);
        case Z3_OP_SGEQ:
            return simplify_ugt_sge(E1, E2);
        case Z3_OP_SLEQ:
            return simplify_ugt_sle(E1, E2);
        default:
            break;
    }
    return E2;
}

static inline z3::expr simplify_sgt(const z3::expr &E1, const z3::expr &E2) {
    switch (E2.decl().decl_kind()) {
        case Z3_OP_EQ:
            return simplify_sgt_eq(E1, E2);
        case Z3_OP_DISTINCT:
            return simplify_sgt_ne(E1, E2);
        case Z3_OP_UGT:
            return simplify_sgt_ugt(E1, E2);
        case Z3_OP_ULT:
            return simplify_sgt_ult(E1, E2);
        case Z3_OP_SGT:
            return simplify_sgt_sgt(E1, E2);
        case Z3_OP_SLT:
            return simplify_sgt_slt(E1, E2);
        case Z3_OP_UGEQ:
            return simplify_sgt_uge(E1, E2);
        case Z3_OP_ULEQ:
            return simplify_sgt_ule(E1, E2);
        case Z3_OP_SGEQ:
            return simplify_sgt_sge(E1, E2);
        case Z3_OP_SLEQ:
            return simplify_sgt_sle(E1, E2);
        default:
            break;
    }
    return E2;
}

static inline z3::expr simplify_uge(const z3::expr &E1, const z3::expr &E2) {
    switch (E2.decl().decl_kind()) {
        case Z3_OP_EQ:
            return simplify_uge_eq(E1, E2);
        case Z3_OP_DISTINCT:
            return simplify_uge_ne(E1, E2);
        case Z3_OP_UGT:
            return simplify_uge_ugt(E1, E2);
        case Z3_OP_ULT:
            return simplify_uge_ult(E1, E2);
        case Z3_OP_SGT:
            return simplify_uge_sgt(E1, E2);
        case Z3_OP_SLT:
            return simplify_uge_slt(E1, E2);
        case Z3_OP_UGEQ:
            return simplify_uge_uge(E1, E2);
        case Z3_OP_ULEQ:
            return simplify_uge_ule(E1, E2);
        case Z3_OP_SGEQ:
            return simplify_uge_sge(E1, E2);
        case Z3_OP_SLEQ:
            return simplify_uge_sle(E1, E2);
        default:
            break;
    }
    return E2;
}

static inline z3::expr simplify_sge(const z3::expr &E1, const z3::expr &E2) {
    switch (E2.decl().decl_kind()) {
        case Z3_OP_EQ:
            return simplify_sge_eq(E1, E2);
        case Z3_OP_DISTINCT:
            return simplify_sge_ne(E1, E2);
        case Z3_OP_UGT:
            return simplify_sge_ugt(E1, E2);
        case Z3_OP_ULT:
            return simplify_sge_ult(E1, E2);
        case Z3_OP_SGT:
            return simplify_sge_sgt(E1, E2);
        case Z3_OP_SLT:
            return simplify_sge_slt(E1, E2);
        case Z3_OP_UGEQ:
            return simplify_sge_uge(E1, E2);
        case Z3_OP_ULEQ:
            return simplify_sge_ule(E1, E2);
        case Z3_OP_SGEQ:
            return simplify_sge_sge(E1, E2);
        case Z3_OP_SLEQ:
            return simplify_sge_sle(E1, E2);
        default:
            break;
    }
    return E2;
}

static inline z3::expr simplify_ult(const z3::expr &E1, const z3::expr &E2) {
    switch (E2.decl().decl_kind()) {
        case Z3_OP_EQ:
            return simplify_ult_eq(E1, E2);
        case Z3_OP_DISTINCT:
            return simplify_ult_ne(E1, E2);
        case Z3_OP_UGT:
            return simplify_ult_ugt(E1, E2);
        case Z3_OP_ULT:
            return simplify_ult_ult(E1, E2);
        case Z3_OP_SGT:
            return simplify_ult_sgt(E1, E2);
        case Z3_OP_SLT:
            return simplify_ult_slt(E1, E2);
        case Z3_OP_UGEQ:
            return simplify_ult_uge(E1, E2);
        case Z3_OP_ULEQ:
            return simplify_ult_ule(E1, E2);
        case Z3_OP_SGEQ:
            return simplify_ult_sge(E1, E2);
        case Z3_OP_SLEQ:
            return simplify_ult_sle(E1, E2);
        default:
            break;
    }
    return E2;
}

static inline z3::expr simplify_ule(const z3::expr &E1, const z3::expr &E2) {
    switch (E2.decl().decl_kind()) {
        case Z3_OP_EQ:
            return simplify_ule_eq(E1, E2);
        case Z3_OP_DISTINCT:
            return simplify_ule_ne(E1, E2);
        case Z3_OP_UGT:
            return simplify_ule_ugt(E1, E2);
        case Z3_OP_ULT:
            return simplify_ule_ult(E1, E2);
        case Z3_OP_SGT:
            return simplify_ule_sgt(E1, E2);
        case Z3_OP_SLT:
            return simplify_ule_slt(E1, E2);
        case Z3_OP_UGEQ:
            return simplify_ule_uge(E1, E2);
        case Z3_OP_ULEQ:
            return simplify_ule_ule(E1, E2);
        case Z3_OP_SGEQ:
            return simplify_ule_sge(E1, E2);
        case Z3_OP_SLEQ:
            return simplify_ule_sle(E1, E2);
        default:
            break;
    }
    return E2;
}

static inline z3::expr simplify_slt(const z3::expr &E1, const z3::expr &E2) {
    switch (E2.decl().decl_kind()) {
        case Z3_OP_EQ:
            return simplify_slt_eq(E1, E2);
        case Z3_OP_DISTINCT:
            return simplify_slt_ne(E1, E2);
        case Z3_OP_UGT:
            return simplify_slt_ugt(E1, E2);
        case Z3_OP_ULT:
            return simplify_slt_ult(E1, E2);
        case Z3_OP_SGT:
            return simplify_slt_sgt(E1, E2);
        case Z3_OP_SLT:
            return simplify_slt_slt(E1, E2);
        case Z3_OP_UGEQ:
            return simplify_slt_uge(E1, E2);
        case Z3_OP_ULEQ:
            return simplify_slt_ule(E1, E2);
        case Z3_OP_SGEQ:
            return simplify_slt_sge(E1, E2);
        case Z3_OP_SLEQ:
            return simplify_slt_sle(E1, E2);
        default:
            break;
    }
    return E2;
}

static inline z3::expr simplify_sle(const z3::expr &E1, const z3::expr &E2) {
    switch (E2.decl().decl_kind()) {
        case Z3_OP_EQ:
            return simplify_sle_eq(E1, E2);
        case Z3_OP_DISTINCT:
            return simplify_sle_ne(E1, E2);
        case Z3_OP_UGT:
            return simplify_sle_ugt(E1, E2);
        case Z3_OP_ULT:
            return simplify_sle_ult(E1, E2);
        case Z3_OP_SGT:
            return simplify_sle_sgt(E1, E2);
        case Z3_OP_SLT:
            return simplify_sle_slt(E1, E2);
        case Z3_OP_UGEQ:
            return simplify_sle_uge(E1, E2);
        case Z3_OP_ULEQ:
            return simplify_sle_ule(E1, E2);
        case Z3_OP_SGEQ:
            return simplify_sle_sge(E1, E2);
        case Z3_OP_SLEQ:
            return simplify_sle_sle(E1, E2);
        default:
            break;
    }
    return E2;
}

z3::expr Z3::simplify(const z3::expr &E1, const z3::expr &E2) {
    if (Z3::is_naming_eq(E1) || Z3::is_naming_eq(E2))
        return E2;

    auto NewE1 = normalize(E1);
    auto NewE2 = normalize(E2);

    if (NewE1.is_or() && (!NewE2.is_or() && !NewE2.is_and())) {
        for (unsigned K = 0; K < NewE1.num_args(); ++K) {
            auto R = simplify(NewE1.arg(K), NewE2);
            if (!R.is_false()) return E2;
        }
        return Z3::bool_val(false);
    }

    if ((!NewE1.is_or() && !NewE1.is_and()) && NewE2.is_or()) {
        auto OrVec = Z3::vec();
        for (unsigned K = 0; K < NewE2.num_args(); ++K) {
            auto R = simplify(NewE1, NewE2.arg(K));
            if (!R.is_false()) OrVec.push_back(R);
        }
        if (OrVec.size() == 1) return OrVec[0];
        if (OrVec.empty()) return Z3::bool_val(false);
        return z3::mk_or(OrVec);
    }

    switch (NewE1.decl().decl_kind()) {
        case Z3_OP_EQ:
            return simplify_eq(NewE1, NewE2);
        case Z3_OP_DISTINCT:
            return simplify_ne(NewE1, NewE2);
        case Z3_OP_UGT:
            return simplify_ugt(NewE1, NewE2);
        case Z3_OP_ULT:
            return simplify_ult(NewE1, NewE2);
        case Z3_OP_SGT:
            return simplify_sgt(NewE1, NewE2);
        case Z3_OP_SLT:
            return simplify_slt(NewE1, NewE2);
        case Z3_OP_UGEQ:
            return simplify_uge(NewE1, NewE2);
        case Z3_OP_ULEQ:
            return simplify_ule(NewE1, NewE2);
        case Z3_OP_SGEQ:
            return simplify_sge(NewE1, NewE2);
        case Z3_OP_SLEQ:
            return simplify_sle(NewE1, NewE2);
        default:
            break;
    }
    return E2;
}