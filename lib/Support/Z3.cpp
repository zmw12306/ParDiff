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

#include "Support/Debug.h"
#include "Support/Z3.h"
#include "Z3Macro.h"

static z3::context Ctx;
static z3::solver Solver(Ctx);
static z3::goal goal(Ctx);
static z3::expr_vector SolverAssumptions(Ctx);
static z3::expr Len(Ctx);
static z3::tactic t(Ctx, "split-clause");
static z3::tactic skip(Ctx, "skip");
static z3::tactic simply(Ctx, "simplify");

void Z3::initialize() {
    pardiff_INFO("Z3 version: " << Z3_get_full_version());
}

z3::expr Z3::bv_val(unsigned V, unsigned Size) {
    return Ctx.bv_val(V, Size);
}

z3::expr Z3::bv_val(int V, unsigned Size) {
    return Ctx.bv_val(V, Size);
}

z3::expr Z3::bv_val(uint64_t V, unsigned Size) {
    return Ctx.bv_val(V, Size);
}

z3::expr Z3::bv_val(int64_t V, unsigned Size) {
    return Ctx.bv_val(V, Size);
}

z3::expr Z3::bv_const(const char *Name, unsigned int Size) {
    return Ctx.bv_const(Name, Size);
}

z3::expr Z3::bool_val(bool B) {
    return Ctx.bool_val(B);
}

z3::expr Z3::bool_const(const char *Name) {
    return Ctx.bool_const(Name);
}
z3::expr Z3::int_const(const char * Name){
    return Ctx.int_const(Name);
}

z3::expr Z3::free_bool() {
    static unsigned I = 0;
    std::string Name(FREE_VAR);
    Name.append(std::to_string(I++));
    return Ctx.bool_const(Name.c_str());
}

z3::expr Z3::free_bv(unsigned Bitwidth) {
    static unsigned K = 0;
    std::string Name(FREE_VAR);
    Name.append(std::to_string(K++));
    return Ctx.bv_const(Name.c_str(), Bitwidth);
}

bool Z3::is_free(const z3::expr &E) {
    return E.is_const() && E.to_string().find(FREE_VAR) != std::string::npos;
}

z3::expr Z3::index_var() {
    static unsigned J = 0;
    std::string Name(INDEX_VAR);
    Name.append(std::to_string(J++));
    return Ctx.bv_const(Name.c_str(), 64);
}

bool Z3::is_index_var(const z3::expr &E) {
    return E.is_bv() && E.is_const() && E.to_string().find(INDEX_VAR) != std::string::npos;
}

z3::expr Z3::length(unsigned Bitwidth) {
    static unsigned K = 0;
    if (K == 0) {
        K++;
        assert(Bitwidth != UINT32_MAX);
        Len = Z3::bv_const(LENGTH, Bitwidth);
        return Len;
    } else {
        assert((Bitwidth == UINT32_MAX || Len.get_sort().bv_size() == Bitwidth) &&
               "Bitwidth of length cannot be changed!");
        return Len;
    }
}

bool Z3::is_length(const z3::expr &E) {
    return E.is_bv() && E.is_const() && E.to_string() == LENGTH;
}

z3::expr Z3::base(unsigned K) {
    std::string Name(BASE);
    Name.append(std::to_string(K));
    return Z3::bv_const(Name.c_str(), 64);
}

bool Z3::is_base(const z3::expr &E) {
    return E.is_bv() && E.is_const() && E.to_string().find(BASE) == 0;
}

z3::expr Z3::trip_count(unsigned K) {
    std::string Name(TRIP_COUNT);
    Name.append(std::to_string(K));
    return Z3::bv_const(Name.c_str(), 64);
}

bool Z3::is_trip_count(const z3::expr &E) {
    return E.is_bv() && E.is_const() && E.to_string().find(TRIP_COUNT) == 0;
}

z3::expr_vector Z3::vec() {
    return {Ctx};
}

z3::expr Z3::packing(const char *Name, const z3::expr_vector &Args, unsigned Ret) {
    z3::sort_vector SortVec(Ctx);
    for (auto E: Args)
        SortVec.push_back(E.get_sort());
    auto RetSort = Ret == 0 ? Ctx.bool_sort() : Ctx.bv_sort(Ret);
    auto Decl = z3::function(Name, SortVec, RetSort);
    return Decl(Args);
}

z3::expr Z3::naming(const z3::expr &E, const char *Name) {
    auto Decl = z3::function(NAME, E.get_sort(), E.get_sort());
    auto Naming = Decl(E);
    auto NameExpr = Z3::bv_const(Name, E.get_sort().bv_size());
    return Naming == NameExpr;
}

bool Z3::is_naming(const z3::expr &E) {
    return E.num_args() == 1 && E.decl().name().str() == NAME;
}

bool Z3::is_naming_eq(const z3::expr &E) {
    if (E.is_eq())
        return is_naming(E.arg(0));
    return false;
}

unsigned Z3::id(const z3::expr &E) {
    return Z3_get_ast_id(Ctx, E);
}

bool Z3::same(const z3::expr &E1, const z3::expr &E2) {
    return Z3_get_ast_id(Ctx, E1) == Z3_get_ast_id(Ctx, E2);
}

bool Z3::is_numeral_i64(const z3::expr &E, int64_t &R) {
    uint64_t Const;
    if (Z3::is_numeral_u64(E, Const)) {
        unsigned OrigBitwidth = E.get_sort().bv_size();
        Const = Const << (64 - OrigBitwidth);
        R = ((int64_t) Const) >> (64 - OrigBitwidth);
        return true;
    }
    return false;
}

bool Z3::is_numeral_u64(const z3::expr &E, uint64_t &R) {
    return E.is_numeral_u64(R);
}

bool Z3::is_zero(const z3::expr &E) {
    uint64_t Const;
    if (Z3::is_numeral_u64(E, Const) && Const == 0) {
        return true;
    }
    return false;
}

bool Z3::find(const z3::expr &Expr, const z3::expr &SubExpr) {
    std::set<unsigned> Visited;
    z3::expr_vector Stack = vec();
    Stack.push_back(Expr);
    while (!Stack.empty()) {
        auto Top = Stack.back();
        Stack.pop_back();
        auto TopID = id(Top);
        if (Visited.count(TopID)) {
            continue;
        }
        Visited.insert(TopID);
        if (Z3::same(Top, SubExpr)) {
            return true;
        }

        auto NumArgs = Top.num_args();
        for (unsigned I = 0; I < NumArgs; ++I) {
            Stack.push_back(Top.arg(I));
        }
    }
    return false;
}

bool Z3::find(const z3::expr & Expr, bool(*P)(const z3::expr &)){
    std::set<unsigned> Visited;
    z3::expr_vector Stack = Z3::vec();
    Stack.push_back(Expr);
    while (!Stack.empty()) {
        auto Top = Stack.back();
        Stack.pop_back();
        auto TopID = id(Top);
        if (Visited.count(TopID)) {
            continue;
        }
        Visited.insert(TopID);
        if (P(Top)) {
           return true;
        }

        auto NumArgs = Top.num_args();
        for (unsigned I = 0; I < NumArgs; ++I) {
            Stack.push_back(Top.arg(I));
        }
    }
    return false;
}

bool Z3::find_byte_index(const z3::expr &Expr, int (*P)(const z3::expr &)){
    std::set<unsigned> Visited;
    z3::expr_vector Stack = vec();
    Stack.push_back(Expr);
    while (!Stack.empty()) {
        auto Top = Stack.back();
        Stack.pop_back();
        auto TopID = id(Top);
        if (Visited.count(TopID)) {
            continue;
        }
        Visited.insert(TopID);
        if (P(Top) == 2) {
            return true;
        }
        else if(P(Top) == 1){
            continue;
        }
        auto NumArgs = Top.num_args();
        for (unsigned I = 0; I < NumArgs; ++I) {
            Stack.push_back(Top.arg(I));
        }
    }
    return false;
}

z3::expr_vector Z3::find_all(const z3::expr &Expr, bool Recursive, bool (*P)(const z3::expr &)) {
    z3::expr_vector Result = vec();

    std::set<unsigned> Visited;
    z3::expr_vector Stack = vec();
    Stack.push_back(Expr);
    while (!Stack.empty()) {
        auto Top = Stack.back();
        Stack.pop_back();
        auto TopID = id(Top);
        if (Visited.count(TopID)) {
            continue;
        }
        Visited.insert(TopID);
        if (P(Top)) {
            Result.push_back(Top);
            if (!Recursive) continue;
        }

        auto NumArgs = Top.num_args();
        for (unsigned I = 0; I < NumArgs; ++I) {
            Stack.push_back(Top.arg(I));
        }
    }
    return Result;
}

//given a expr vector V, return a expr vector which contains all the expr in V satisfied P
z3::expr_vector Z3::find_all(const z3::expr_vector &vec, bool (*P)(const z3::expr &)){
    z3::expr_vector Result = Z3::vec();
    for(auto exp: vec){
        if(P(exp))
            Result.push_back(exp);
    }
    return Result;
}

template<typename OpKind>
static void postVisit(const z3::expr &Expr, OpKind P, z3::expr_vector Ret, std::set<unsigned> *Visited) {
    if (Visited) {
        if (Visited->count(Z3::id(Expr)))
            return;
        Visited->insert(Z3::id(Expr));
    }

    if (!P(Expr)) {
        Ret.push_back(Expr);
        return;
    }
    auto NumArgs = Expr.num_args();
    for (unsigned I = 0; I < NumArgs; ++I) {
        postVisit(Expr.arg(I), P, Ret, Visited);
    }
}

z3::expr_vector Z3::find_consecutive_ops(const z3::expr &Expr, bool (*P)(const z3::expr &), bool AllowRep) {
    z3::expr_vector Result = vec();
    if (!AllowRep) {
        std::set<unsigned> Visited;
        postVisit(Expr, P, Result, &Visited);
    } else {
        postVisit(Expr, P, Result, nullptr);
    }
    return Result;
}

z3::expr_vector Z3::find_consecutive_ops(const z3::expr &Expr, Z3_decl_kind OpKind, bool AllowRep) {
    auto P = [OpKind](const z3::expr &E) { return E.decl().decl_kind() == OpKind; };
    z3::expr_vector Result = vec();
    if (!AllowRep) {
        std::set<unsigned> Visited;
        postVisit(Expr, P, Result, &Visited);
    } else {
        postVisit(Expr, P, Result, nullptr);
    }
    return Result;
}

z3::expr_vector Z3::find_consecutive_ops(const z3::expr &Expr, const char *OpName, bool AllowRep) {
    auto P = [OpName](const z3::expr &E) { return E.decl().name().str() == OpName; };
    z3::expr_vector Result = vec();
    if (!AllowRep) {
        std::set<unsigned> Visited;
        postVisit(Expr, P, Result, &Visited);
    } else {
        postVisit(Expr, P, Result, nullptr);
    }
    return Result;
}


bool Z3::is_distinct_or_not_eq(const z3::expr &E) {
    if (E.is_distinct()) return true;
    if (E.is_not() && E.arg(0).is_eq()) return true;
    return false;
}

static std::string to_string_template(const z3::expr &Expr, const char *Op) {
    std::string Ret;
    for (unsigned I = 0; I < Expr.num_args(); ++I) {
        Ret.append(Z3::to_string(Expr.arg(I)));
        if (I != Expr.num_args() - 1) {
            Ret.append(" ").append(Op).append(" ");
        }
    }
    return Ret;
}

static std::string to_string_default(const z3::expr &Expr) {
    //bool Phi = Z3::is_phi(Expr);
    auto Decl = Expr.decl();
    std::string Ret = Decl.name().str();

    if (Ret == BYTE_ARRAY_RANGE) {
         Ret = "B[";
         Ret += Z3::to_string(Expr.arg(0));
         Ret += "..";
         Ret += Z3::to_string(Expr.arg(1));
         Ret += "]";
         return Ret;
     }

     bool Phi = Z3::is_phi(Expr);
    unsigned NumParams = Z3_get_decl_num_parameters(Ctx, Decl);
    unsigned NumArgs = Expr.num_args();
    if (NumParams + NumArgs > 0) {
        Ret.append("(");
        for (unsigned I = 0; I < NumArgs + NumParams; ++I) {
            if (I < NumArgs) {
                if (!Phi) {
                    Ret.append(Z3::to_string(Expr.arg(I)));
                } else {
                    Ret.append(Z3::to_string(Expr.arg(I))).append(", ");
                    auto CondID = Z3::phi_cond_id(Z3::phi_id(Expr), I);
                    Ret.append("$").append(std::to_string(CondID));
                }
            } else {
                auto ParamKind = Z3_get_decl_parameter_kind(Ctx, Decl, I - NumArgs);
                switch (ParamKind) {
                    case Z3_PARAMETER_INT:
                        Ret.append(std::to_string(Z3_get_decl_int_parameter(Ctx, Decl, I - NumArgs)));
                        break;
                    case Z3_PARAMETER_DOUBLE:
                    case Z3_PARAMETER_RATIONAL:
                    case Z3_PARAMETER_SYMBOL:
                    case Z3_PARAMETER_SORT:
                    case Z3_PARAMETER_AST:
                    case Z3_PARAMETER_FUNC_DECL:
                        Ret.append("?");
                        break;
                }
            }
            if (I != NumArgs + NumParams - 1) {
                Ret.append(", ");
            }
        }
        Ret.append(")");
    }

    return Ret;
}

std::string Z3::to_string(const z3::expr &Expr, bool Easy) {
    if (!Easy)
        return Expr.to_string();
    int64_t Num64;
    if (Z3::is_numeral_i64(Expr, Num64)) {
        if (Expr.get_sort().bv_size() > 4)
            return std::to_string(Num64);
        else
            return Expr.to_string();
    } else {
        auto Kind = Expr.decl().decl_kind();
        switch (Kind) {
            case Z3_OP_TRUE:
                return "true";
            case Z3_OP_FALSE:
                return "false";
            case Z3_OP_SELECT: {
                std::string Ret(to_string(Expr.arg(0)));
                Ret.append("[").append(to_string(Expr.arg(1))).append("]");
                return Ret;
            }
            case Z3_OP_EQ: {
                std::string Ret(to_string(Expr.arg(0)));
                Ret.append(" = ").append(to_string(Expr.arg(1)));
                return Ret;
            }
            case Z3_OP_DISTINCT: {
                std::string Ret(to_string(Expr.arg(0)));
                Ret.append(" ≠ ").append(to_string(Expr.arg(1)));
                return Ret;
            }
            case Z3_OP_CONCAT: {
                std::string Ret;
                unsigned K = 0;
                auto Head = Expr.arg(K);
                int64_t Zero;
                if (Z3::is_numeral_i64(Head, Zero) && Zero == 0) {
                    K++;
                    assert(K < Expr.num_args());
                } else if (Head.get_sort().bv_size() == 1 && Head.decl().decl_kind() == Z3_OP_EXTRACT) {
                    unsigned J = 1;
                    for (; J < Expr.num_args(); ++J) {
                        if (!Z3::same(Expr.arg(J), Head)) break;
                    }
                    if (J < Expr.num_args() && Z3::same(Head.arg(0), Expr.arg(J))) {
                        K = J;
                    }
                }

                for (unsigned I = K; I < Expr.num_args(); ++I)
                    Ret.append(to_string(Expr.arg(I)));
                return Ret;
            }
            case Z3_OP_ADD:
            case Z3_OP_BADD: {
                return to_string_template(Expr, "+");
            }
            case Z3_OP_SUB:
            case Z3_OP_BSUB: {
                return to_string_template(Expr, "-");
            }
            case Z3_OP_MUL:
            case Z3_OP_BMUL: {
                return to_string_template(Expr, "x");
            }
            case Z3_OP_DIV:
            case Z3_OP_BSDIV_I:
            case Z3_OP_BSDIV:
            case Z3_OP_BUDIV_I:
            case Z3_OP_BUDIV: {
                return to_string_template(Expr, "/");
            }
            case Z3_OP_MOD:
            case Z3_OP_REM:
            case Z3_OP_BSMOD:
            case Z3_OP_BSMOD_I:
            case Z3_OP_BSREM:
            case Z3_OP_BSREM_I:
            case Z3_OP_BUREM:
            case Z3_OP_BUREM_I: {
                return to_string_template(Expr, "%");
            }
            case Z3_OP_AND: {
                return to_string_template(Expr, "&&");
            }
            case Z3_OP_BAND: {
                return to_string_template(Expr, "&");
            }
            case Z3_OP_OR: {
                return to_string_template(Expr, "||");
            }
            case Z3_OP_BOR: {
                return to_string_template(Expr, "|");
            }
            case Z3_OP_XOR3:
            case Z3_OP_BXOR:
            case Z3_OP_XOR: {
                return to_string_template(Expr, "^");
            }
            case Z3_OP_GE:
            case Z3_OP_SGEQ:
            case Z3_OP_UGEQ: {
                return to_string_template(Expr, "≥");
            }
            case Z3_OP_LE:
            case Z3_OP_SLEQ:
            case Z3_OP_ULEQ: {
                return to_string_template(Expr, "≤");
            }
            case Z3_OP_GT:
            case Z3_OP_SGT:
            case Z3_OP_UGT: {
                return to_string_template(Expr, ">");
            }
            case Z3_OP_LT:
            case Z3_OP_SLT:
            case Z3_OP_ULT: {
                return to_string_template(Expr, "<");
            }
            case Z3_OP_BLSHR: {
                return to_string_template(Expr, ">>>");
            }
            case Z3_OP_BASHR: {
                return to_string_template(Expr, ">>");
            }
            case Z3_OP_BSHL: {
                return to_string_template(Expr, "<<");
            }
            case Z3_OP_BNOT: {
                return "~" + to_string(Expr.arg(0));
            }
            case Z3_OP_NOT: {
                return "NOT(" + to_string(Expr.arg(0)) + ")";
            }
            case Z3_OP_UMINUS: {
                return "-" + to_string(Expr.arg(0));
            }
            case Z3_OP_SIGN_EXT:
            case Z3_OP_ZERO_EXT:
            case Z3_OP_BV2INT: {
                return to_string(Expr.arg(0));
            }
            case Z3_OP_ITE: {
                return to_string(Expr.arg(0)) + " ? " + to_string(Expr.arg(1)) + " : " + to_string(Expr.arg(2));
            }
            default: {
                return to_string_default(Expr);
            }
        }
    }
}

static Z3::Z3Format PrintFormat = Z3::ZF_Easy;

raw_ostream &operator<<(llvm::raw_ostream &O, const Z3::Z3Format &F) {
    PrintFormat = F;
    return O;
}

raw_ostream &operator<<(llvm::raw_ostream &O, const z3::expr &E) {
    switch (PrintFormat) {
        case Z3::ZF_Orig:
            O << E.to_string();
            break;
        case Z3::ZF_Easy:
            O << Z3::to_string(E);
            break;
        case Z3::ZF_SMTLib:
            O << Z3_benchmark_to_smtlib_string(Ctx, 0, 0, 0, 0, 0, 0, E);
            break;
    }
    PrintFormat = Z3::ZF_Easy; // reset
    return O;
}

void Z3Solver::addAssumption(const z3::expr &A) {
    SolverAssumptions.push_back(A);
}

void Z3Solver::clearAssumptions() {
    SolverAssumptions = Z3::vec();
}

bool Z3Solver::check(const z3::expr &A, std::vector<uint8_t> &Ret) {
    Solver.reset();
    Solver.add(A);
    auto Result = Solver.check();
    if (Result != z3::sat) {
        Ret.clear();
        return false;
    }
    auto Model = Solver.get_model();
    std::vector<bool> Set(Ret.size(), false);
    for (unsigned K = 0; K < Model.num_consts(); ++K) {
        auto Decl = Model.get_const_decl(K);
        auto Interp = Model.get_const_interp(Decl);
        auto DeclName = Decl.name().str();

        if (DeclName == LENGTH) {
            uint64_t LenConst;
            bool Const = Z3::is_numeral_u64(Interp, LenConst);
            assert(Const);
            Ret.resize(LenConst);
            Set.resize(LenConst, false);
        } else if (DeclName == BYTE_ARRAY) {
            while (Interp.decl().decl_kind() == Z3_OP_STORE) {
                uint64_t Index;
                bool Const = Z3::is_numeral_u64(Interp.arg(1), Index);
                assert(Const);
                uint64_t Val;
                Const = Z3::is_numeral_u64(Interp.arg(2), Val);
                assert(Const);
                if (Index >= Ret.size()) {
                    Ret.resize(Index + 1);
                    Set.resize(Index + 1, false);
                }
                if (!Set[Index]) {
                    Ret[Index] = (uint8_t) Val;
                    Set[Index] = true;
                }

                Interp = Interp.arg(0);
            }
            if (Interp.decl().decl_kind() == Z3_OP_CONST_ARRAY) {
                uint64_t Val;
                bool Const = Z3::is_numeral_u64(Interp.arg(0), Val);
                assert(Const);
                for (unsigned J = 0; J < Set.size(); ++J) {
                    if (!Set[J]) {
                        Ret[J] = Val;
                    }
                }
            }
        }
    }
    return true;
}

bool Z3Solver::check(const z3::expr &A) {
    Solver.reset();
    Solver.add(A);
    return Solver.check() == z3::sat;
}

bool Z3Solver::check(const std::vector<z3::expr> &V) {
    Solver.reset();
    for (auto &E: V) Solver.add(E);
    auto Result = Solver.check();
    assert(Result != z3::unknown);
    return Result == z3::sat;
}

bool Z3Solver::check(const z3::expr_vector &V) {
    Solver.reset();
    for (auto E: V) Solver.add(E);
    auto Result = Solver.check();
    assert(Result != z3::unknown);
    return Result == z3::sat;
}

void Z3Solver::getmodel(const z3::expr &A, const z3::expr &F1, const z3::expr &F2){
    
    Solver.reset();
    Solver.add(A);
    Solver.add(Z3::length() > 0);
    //Solver.add(Z3::length() = );

    //std::cout <<"Solver:: "<< Solver << "\n";
    if(Solver.check() == z3::sat){
        //std::cout <<"Solver:: "<< Solver << "\n";
        auto Model = Solver.get_model();
        //outs() <<"counterexample: "<< Model << "\n";
        for (unsigned i = 0; i < Model.size(); i++) {
            auto v = Model[i];
            // this problem contains only constants
            assert(v.arity() == 0); 
            errs() << v.name().str() << " = " << Model.get_const_interp(v) << "\n";

        }
        if((Model.eval(F1)).to_string() == "false"){
            errs()<< "F1: false\n";
            Solver.reset();
            goal.reset();
            z3::expr p1 = Z3::bool_const("p1");
            z3::expr p2 = Z3::bool_const("p2");
            Solver.add(implies(p1,F1.simplify()));
            goal.add(F1);

            for (unsigned K = 0; K < Model.num_consts(); ++K){
                auto Decl = Model.get_const_decl(K);
                auto Interp = Model.get_const_interp(Decl);
                auto DeclName = Decl.name().str();

                if (DeclName == LENGTH) {
                    uint64_t LenConst;
                    bool Const = Z3::is_numeral_u64(Interp, LenConst);
                    assert(Const);
                    Solver.add(implies(p2,Z3::length() == (int)LenConst));
                    goal.add(Z3::length() == (int)LenConst);
                
                } else if (DeclName == BYTE_ARRAY) {
                    

                    while (Interp.decl().decl_kind() == Z3_OP_STORE) {
                        uint64_t Index;
                        bool Const1 = Z3::is_numeral_u64(Interp.arg(1), Index);
                        assert(Const1);
                        uint64_t Val;
                        bool Const2 = Z3::is_numeral_u64(Interp.arg(2), Val);
                        assert(Const2);
                        z3::expr model = Z3::byte_array_element(Z3::byte_array(), Interp.arg(1)) == Interp.arg(2);
                       
                        Solver.add(implies(p2,model));
                        goal.add(model);

                        Interp = Interp.arg(0);



                    }

                }

            }
            z3::expr assumptions[2] = {p1, p2};
            //outs()<<Solver.check(2, assumptions)<<"\n";
            z3::expr_vector core = Solver.unsat_core();
            //outs() << "unsat_core size: " << core.size() << "\n";
            for (unsigned i = 0; i < core.size(); i++) {
                errs() << core[i] << "\n";
            }
            z3::tactic split_all = z3::repeat(t | skip);    
            z3::apply_result res = split_all(goal);
            for (unsigned i = 0; i < res.size(); i++) {
                errs() << "subgoal " << i << "\n";
                Solver.reset();
                std::vector<z3::expr> qs;
                z3::goal subgoal =res[i];
                for(unsigned j= 0; j < subgoal.size(); j++){
                    errs() << "Creating answer literal q" << j << " for " << subgoal[j] << "\n";
                    std::stringstream qname; qname << "q" << j;
                    z3::expr qi = Z3::bool_const(qname.str().c_str()); // create a new answer literal
                    Solver.add(implies(qi, subgoal[j]));
                    qs.push_back(qi);
                }
        
                errs() <<Solver.check(static_cast<unsigned>(qs.size()), &qs[0])<< "\n";
                z3::expr_vector core2 = Solver.unsat_core();
                //outs() << core2 << "\n";
                errs() << "size: " << core2.size() << "\n";
                for (unsigned i = 0; i < core2.size(); i++) {
                    errs() << core2[i] << "\n";
                }
            }

            errs() << "end unsat core for the protocol\n";

        }

        else if((Model.eval(F2)).to_string() == "false"){
            errs()<< "F2: false\n";
            Solver.reset();
            goal.reset();
            z3::expr p1 = Z3::bool_const("p1");
            z3::expr p2 = Z3::bool_const("p2");
            Solver.add(implies(p1,F2.simplify()));
            goal.add(F2);

            for (unsigned K = 0; K < Model.num_consts(); ++K){
                auto Decl = Model.get_const_decl(K);
                auto Interp = Model.get_const_interp(Decl);
                auto DeclName = Decl.name().str();

                if (DeclName == LENGTH) {
                    uint64_t LenConst;
                    bool Const = Z3::is_numeral_u64(Interp, LenConst);
                    assert(Const);
                    Solver.add(implies(p2,Z3::length() == (int)LenConst));
                    goal.add(Z3::length() == (int)LenConst);
                
                } else if (DeclName == BYTE_ARRAY) {
                    

                    while (Interp.decl().decl_kind() == Z3_OP_STORE) {
                        uint64_t Index;
                        bool Const1 = Z3::is_numeral_u64(Interp.arg(1), Index);
                        assert(Const1);
                        uint64_t Val;
                        bool Const2 = Z3::is_numeral_u64(Interp.arg(2), Val);
                        assert(Const2);
                        z3::expr model = Z3::byte_array_element(Z3::byte_array(), Interp.arg(1)) == Interp.arg(2);
                       
                        Solver.add(implies(p2,model));
                        goal.add(model);

                        Interp = Interp.arg(0);


                    }
                    // if (Interp.decl().decl_kind() == Z3_OP_CONST_ARRAY) {
                    //     uint64_t Val;
                    //     bool Const = Z3::is_numeral_u64(Interp.arg(0), Val);
                    //     assert(Const);
                    //     for (unsigned J = 0; J < Set.size(); ++J) {
                    //         if (!Set[J]) {
                    //             Ret[J] = Val;
                    //         }
                    //     }
                    // }

                }

            }
            
            z3::expr assumptions[2] = {p1, p2};
            //outs()<<Solver.check(2, assumptions)<<"\n";
            z3::expr_vector core = Solver.unsat_core();
            //outs() << "unsat_core size: " << core.size() << "\n";
            for (unsigned i = 0; i < core.size(); i++) {
                errs() << core[i] << "\n";
            }
            z3::tactic split_all = z3::repeat(t | skip);    
            z3::apply_result res = split_all(goal);
            for (unsigned i = 0; i < res.size(); i++) {
                errs() << "subgoal " << i << "\n";
                Solver.reset();
                std::vector<z3::expr> qs;
                z3::goal subgoal =res[i];
                for(unsigned j= 0; j < subgoal.size(); j++){
                    errs() << "Creating answer literal q" << j << " for " << subgoal[j] << "\n";
                    std::stringstream qname; qname << "q" << j;
                    z3::expr qi = Z3::bool_const(qname.str().c_str()); // create a new answer literal
                    Solver.add(implies(qi, subgoal[j]));
                    qs.push_back(qi);
                }
        
                errs() <<Solver.check(static_cast<unsigned>(qs.size()), &qs[0])<< "\n";
                z3::expr_vector core2 = Solver.unsat_core();
                //outs() << core2 << "\n";
                errs() << "size: " << core2.size() << "\n";
                for (unsigned i = 0; i < core2.size(); i++) {
                    errs() << core2[i] << "\n";
                }
            }

            errs() << "end unsat core for the protocol\n";
        }
       

    }
    else{
        errs()<<"the expr for getmodel is unsat!!\n";
    }
    
}

