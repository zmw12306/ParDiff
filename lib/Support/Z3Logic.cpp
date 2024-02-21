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

z3::expr Z3::negation(const z3::expr &E) {
    assert(E.is_bool());
    auto Decl = E.decl();
    switch (Decl.decl_kind()) {
        case Z3_OP_NOT:
            return E.arg(0);
        case Z3_OP_UGT:
            return Z3::ule(E.arg(0), E.arg(1));
        case Z3_OP_UGEQ:
            return Z3::ult(E.arg(0), E.arg(1));
        case Z3_OP_ULT:
            return Z3::uge(E.arg(0), E.arg(1));
        case Z3_OP_ULEQ:
            return Z3::ugt(E.arg(0), E.arg(1));
        case Z3_OP_SGT:
            return Z3::sle(E.arg(0), E.arg(1));
        case Z3_OP_SGEQ:
            return Z3::slt(E.arg(0), E.arg(1));
        case Z3_OP_SLT:
            return Z3::sge(E.arg(0), E.arg(1));
        case Z3_OP_SLEQ:
            return Z3::sgt(E.arg(0), E.arg(1));
        case Z3_OP_EQ:
            return Z3::ne(E.arg(0), E.arg(1));
        case Z3_OP_DISTINCT:
            return Z3::eq(E.arg(0), E.arg(1));
        case Z3_OP_TRUE:
            return bool_val(false);
        case Z3_OP_FALSE:
            return bool_val(true);
        case Z3_OP_OR: {
            auto Vec = Z3::find_consecutive_ops(E, Z3_OP_OR);
            auto RetVec = vec();
            for (auto Expr: Vec) {
                RetVec.push_back(Z3::negation(Expr));
            }
            return Z3::make_and(RetVec);
        }
        case Z3_OP_AND:
        default:
            if (is_free(E)) {
                return free_bool();
            } else if (is_phi(E)) {
                auto ResultVec = Z3::vec();
                for (unsigned K = 0; K < E.num_args(); ++K) {
                    ResultVec.push_back(negation(E.arg(K)));
                }
                return Z3::make_phi(Z3::phi_id(E), ResultVec);
            }
            return !E;
    }
}

z3::expr Z3::make_and(const z3::expr &E1, const z3::expr &E2) {
    auto Vec = vec();
    Vec.push_back(E1);
    Vec.push_back(E2);
    return make_and(Vec);
}

z3::expr Z3::make_and(const std::vector<z3::expr> &Vec) {
    auto Z3Vec = Z3::vec();
    for (unsigned K = 0; K < Vec.size(); ++K)
        Z3Vec.push_back(Vec[K]);
    return make_and(Z3Vec);
}

z3::expr Z3::make_and(const z3::expr_vector &Vec) {
    if (Vec.empty())
        return free_bool();
    std::set<unsigned> Added;
    std::vector<z3::expr> AndVec;
    bool HasFree = false;
    for (unsigned K = 0; K < Vec.size(); ++K) {
        auto Exprs = find_consecutive_ops(Vec[K], Z3_OP_AND);
        for (auto Expr: Exprs) {
            if (Added.count(id(Expr)) || Expr.is_true()) {
                continue;
            }
            if (is_free(Expr)) {
                HasFree = true;
                continue;
            }
            if (Expr.is_false())
                return Z3::bool_val(false);
            AndVec.push_back(Expr);
            Added.insert(id(Expr));
        }
    }
    if (AndVec.size() == 1)
        return AndVec[0];
    if (AndVec.empty())
        return HasFree ? free_bool() : Z3::bool_val(true);

    auto AndVec2 = Z3::vec();
    AndVec2.push_back(AndVec[0]);
    for (unsigned K = 1; K < AndVec.size(); ++K) {
        auto A = AndVec2.back();
        auto B = AndVec[K];
        if (!Z3::is_phi(A) || !Z3::is_phi(B) || Z3::phi_id(A) != Z3::phi_id(B)) {
            AndVec2.push_back(B);
            continue;
        }

        auto PhiVec = Z3::vec();
        for (unsigned J = 0; J < A.num_args(); ++J) {
            auto AA = A.arg(J);
            auto BB = B.arg(J);
            if (AA.is_false()) {
                PhiVec.push_back(Z3::bool_val(false));
            } else if (AA.is_true()) {
                PhiVec.push_back(BB);
            } else if (Z3::is_free(AA)) {
                if (BB.is_false()) PhiVec.push_back(Z3::bool_val(false));
                else if (BB.is_true() || Z3::is_free(BB)) PhiVec.push_back(Z3::free_bool());
                else break;
            } else {
                break;
            }
        }
        if (PhiVec.size() == A.num_args()) {
            auto NewPhi = Z3::make_phi(Z3::phi_id(A), PhiVec);
            AndVec2.set(AndVec2.size() - 1, NewPhi);
        } else {
            AndVec2.push_back(B);
        }
    }
    assert(!AndVec2.empty());
    if (AndVec2.size() == 1)
        return AndVec2[0];
    return z3::mk_and(AndVec2);
}

z3::expr Z3::make_or(const z3::expr &E1, const z3::expr &E2) {
    auto Vec = vec();
    Vec.push_back(E1);
    Vec.push_back(E2);
    return make_or(Vec);
}

z3::expr Z3::make_or(const std::vector<z3::expr> &Vec) {
    auto Z3Vec = Z3::vec();
    for (auto E: Vec)
        Z3Vec.push_back(E);
    return make_or(Z3Vec);
}

z3::expr Z3::make_or(const z3::expr_vector &Vec) {
    if (Vec.empty())
        return free_bool();
    std::set<unsigned> Added;
    std::vector<z3::expr> OrVec;
    bool HasFree = false;
    for (auto E: Vec) {
        auto Exprs = find_consecutive_ops(E, Z3_OP_OR);
        for (auto Expr: Exprs) {
            if (Added.count(id(Expr)) || Expr.is_false()) {
                continue;
            }
            if (is_free(Expr)) {
                HasFree = true;
                continue;
            }
            if (Expr.is_true()) {
                return Z3::bool_val(true);
            }
            OrVec.push_back(Expr);
            Added.insert(id(Expr));
        }
    }
    if (OrVec.size() == 1)
        return OrVec[0];
    if (OrVec.empty())
        return HasFree ? free_bool() : Z3::bool_val(false);

    std::sort(OrVec.begin(), OrVec.end(), [](const z3::expr &A, const z3::expr &B) {
        unsigned APhiID = Z3::is_phi(A) ? Z3::phi_id(A) : UINT32_MAX;
        unsigned BPhiID = Z3::is_phi(B) ? Z3::phi_id(B) : UINT32_MAX;
        return APhiID < BPhiID;
    });

    auto OrVec2 = Z3::vec();
    OrVec2.push_back(OrVec[0]);
    for (unsigned K = 1; K < OrVec.size(); ++K) {
        auto A = OrVec2.back();
        auto B = OrVec[K];
        if (!Z3::is_phi(A) || !Z3::is_phi(B) || Z3::phi_id(A) != Z3::phi_id(B)) {
            OrVec2.push_back(B);
            continue;
        }

        auto PhiVec = Z3::vec();
        for (unsigned J = 0; J < A.num_args(); ++J) {
            auto AA = A.arg(J);
            auto BB = B.arg(J);
            PhiVec.push_back(Z3::make_or(AA, BB));
        }
        if (PhiVec.size() == A.num_args()) {
            auto NewPhi = Z3::make_phi(Z3::phi_id(A), PhiVec);
            OrVec2.set(OrVec2.size() - 1, NewPhi);
        } else {
            OrVec2.push_back(B);
        }
    }
    assert(!OrVec2.empty());
    if (OrVec2.size() == 1)
        return OrVec2[0];
    return z3::mk_or(OrVec2);
}