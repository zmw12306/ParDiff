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
#include "Support/Z3.h"

static std::map<unsigned, z3::expr_vector> PhiID2CondMap;
static std::map<unsigned, std::pair<BasicBlock *, std::vector<BasicBlock *>>> PhiID2BlockMap;

z3::expr Z3::ite(const z3::expr &C, const z3::expr &O1, const z3::expr &O2) {
    if (C.is_not())
        return Z3::ite(C.arg(0), O2, O1);
    if (C.is_distinct())
        return Z3::ite(C.arg(0) == C.arg(1), O2, O1);
    if (C.is_false())
        return O2;
    if (C.is_true())
        return O1;

    uint64_t Zero;
    if (C.is_eq() && Z3::is_numeral_u64(C.arg(1), Zero) && !Zero) {
        // a = 0 ? x : x + a; => x + a
        auto From = Z3::vec();
        auto To = Z3::vec();
        From.push_back(C.arg(0));
        To.push_back(C.arg(1));
        z3::expr O2Cp = O2;
        if (Z3::same(O2Cp.substitute(From, To).simplify(), O1.simplify())) {
            return O2;
        }
    }
    return z3::ite(C, O1, O2);
}

static z3::expr simplify_phi(const z3::expr &Phi, const z3::expr_vector &CondVec) {
    // some rewriting rules
    if (Phi.num_args() == 2) {
        auto Val1 = Phi.arg(0);
        auto Con1 = CondVec[0];
        auto Val2 = Phi.arg(1);
        auto Con2 = CondVec[1];
        if ((Con1 && Con2).simplify().is_false()) {
            // phi(x, a = 0 ; x + a, a != 0) => x + a
            if (Con1.is_eq()) {
                auto Ret = Z3::ite(Con1.simplify(), Val1, Val2).simplify();
                return Z3::same(Ret, Val1) || Z3::same(Ret, Val2) ? Ret : Phi;
            } else if (Con2.is_eq()) {
                auto Ret = Z3::ite(Con2.simplify(), Val2, Val1).simplify();
                return Z3::same(Ret, Val1) || Z3::same(Ret, Val2) ? Ret : Phi;
            }
        }
    }
    return Phi;
}

static z3::expr select_phi_arg(unsigned ID, unsigned EID, const z3::expr &E,
                               std::map<z3::expr, z3::expr, Z3::less_than> &SimplifyMap) {
    if (E.is_const()) {
        return E;
    } else if (SimplifyMap.count(E)) {
        return SimplifyMap.at(E);
    } else if (Z3::is_phi(E) && Z3::phi_id(E) == ID) {
        auto Ret = select_phi_arg(ID, EID, E.arg(EID), SimplifyMap);
        SimplifyMap.insert(std::make_pair(E, Ret));
        return Ret;
    } else {
        auto Decl = E.decl();
        auto Vec = Z3::vec();
        for (unsigned K = 0; K < E.num_args(); ++K) {
            Vec.push_back(select_phi_arg(ID, EID, E.arg(K), SimplifyMap));
        }
        auto Ret = Decl(Vec).simplify();
        SimplifyMap.insert(std::make_pair(E, Ret));
        return Ret;
    }
}

z3::expr Z3::select_phi_arg(unsigned int PhiID, unsigned int ArgID, const z3::expr &Expr) {
    std::map<z3::expr, z3::expr, Z3::less_than> SimplifyMap;
    return ::select_phi_arg(PhiID, ArgID, Expr, SimplifyMap);
}

z3::expr Z3::make_phi(unsigned ID, const z3::expr_vector &ValVec, const z3::expr_vector &CondVec) {
    assert(!ValVec.empty());
    assert(ValVec.size() == CondVec.size());

    bool AllFreeBV = true;
    std::set<z3::expr, Z3::less_than> ValSet;
    z3::expr_vector NewValVec = Z3::vec();
    std::vector<z3::sort> SortVec;
    for (int I = 0; I < ValVec.size(); ++I) {
        auto Arg = select_phi_arg(ID, I, ValVec[I]);
        auto Cond = CondVec[I];
        NewValVec.push_back(Arg);
        assert(Cond.is_bool());
        ValSet.insert(Arg);
        if (AllFreeBV && !is_free(Arg)) AllFreeBV = false;

        SortVec.push_back(Arg.get_sort());
    }
    if (ValSet.size() == 1) return *ValSet.begin();
    if (AllFreeBV) return ValSet.begin()->is_bv() ? free_bv(ValSet.begin()->get_sort().bv_size()) : free_bool();

    std::string PhiDeclName(PHI".");
    PhiDeclName.append(std::to_string(ID));
    auto NewPhi = z3::function(PhiDeclName.c_str(), NewValVec.size(), &SortVec[0], SortVec[0]);
    auto RetPhi = simplify_phi(NewPhi(NewValVec), CondVec);
    if (!Z3::is_phi(RetPhi)) return RetPhi;

    // we create a phi, so let's record the phi cond id
    auto It = PhiID2CondMap.find(ID);
    if (It == PhiID2CondMap.end()) {
        PhiID2CondMap.insert(std::make_pair(ID, CondVec));
    } else {
        It->second = CondVec;
    }

    return RetPhi;
}

z3::expr Z3::make_phi(unsigned ID, const z3::expr_vector &ValVec) {
    return make_phi(ID, ValVec, PhiID2CondMap.at(ID));
}

bool Z3::is_phi(const z3::expr &Expr) {
    if (Expr.is_const()) return false;
    auto DeclName = Expr.decl().name().str();
    return StringRef(DeclName).startswith(PHI);
}

bool Z3::same_phi(const z3::expr &O1, const z3::expr &O2) {
    if (O1.num_args() != O2.num_args()) return false;
    if (!Z3::is_phi(O1) || !Z3::is_phi(O2)) return false;
    return O1.decl().name().str() == O2.decl().name().str();
}

unsigned Z3::phi_id(const z3::expr &Expr) {
    assert(is_phi(Expr));
    auto DeclName = Expr.decl().name().str();
    // phi.4, phi.15, etc.
    std::string IDStr = StringRef(DeclName).substr(4).str();
    return std::strtoul(IDStr.c_str(), nullptr, 10);
}

unsigned Z3::phi_cond_id(unsigned PhiID, unsigned K) {
    auto It = PhiID2CondMap.find(PhiID);
    assert (It != PhiID2CondMap.end());
    auto Cond = It->second[K];
    return Z3::id(Cond);
}

z3::expr_vector Z3::phi_cond(unsigned PhiID) {
    auto It = PhiID2CondMap.find(PhiID);
    if (It == PhiID2CondMap.end()) {
        return Z3::vec();
    } else {
        return It->second;
    }
}

bool Z3::has_phi(unsigned PhiID) {
    return PhiID2CondMap.count(PhiID);
}

void Z3::bind_phi_id(unsigned PhiID, BasicBlock *MergePoint, const std::vector<BasicBlock *> &Preds) {
    assert(!PhiID2BlockMap.count(PhiID));
    auto &Pair = PhiID2BlockMap[PhiID];
    Pair.first = MergePoint;
    Pair.second = Preds;
}

BasicBlock *Z3::phi_block(unsigned PhiID) {
    auto It = PhiID2BlockMap.find(PhiID);
    if (It != PhiID2BlockMap.end()) {
        return It->second.first;
    }
    return nullptr;
}

const std::vector<BasicBlock *> *Z3::phi_predecessor_blocks(unsigned PhiID) {
    auto It = PhiID2BlockMap.find(PhiID);
    if (It != PhiID2BlockMap.end()) {
        return &It->second.second;
    }
    return nullptr;
}
