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

#ifndef SUPPORT_Z3_H
#define SUPPORT_Z3_H

#include <llvm/ADT/StringRef.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/Debug.h>
#include <llvm/Support/raw_ostream.h>
#include <map>
#include <set>
#include <z3++.h>

using namespace llvm;

class Z3 {
public:
    enum Z3Format {
        ZF_Orig,
        ZF_Easy,
        ZF_SMTLib
    };

public:
    /// call only at initialization
    static void initialize();

    /// create new single values or consts
    /// @{
    static z3::expr bv_val(unsigned, unsigned);

    static z3::expr bv_val(int, unsigned);

    static z3::expr bv_val(uint64_t, unsigned);

    static z3::expr bv_val(int64_t, unsigned);

    static z3::expr bv_const(const char *, unsigned);

    static z3::expr bool_val(bool);

    static z3::expr bool_const(const char *);

    static z3::expr int_const(const char * Name);

    /// @}

    /// @{
    static z3::expr free_bool();

    static z3::expr free_bv(unsigned);

    static bool is_free(const z3::expr &);

    static z3::expr index_var();

    static bool is_index_var(const z3::expr &);

    static z3::expr length(unsigned = UINT32_MAX);

    static bool is_length(const z3::expr &);

    static z3::expr base(unsigned ID);

    static bool is_base(const z3::expr &);

    static z3::expr trip_count(unsigned ID);

    static bool is_trip_count(const z3::expr &);
    /// @}

    /// create a new expr vector, which is essentially a shared ptr of vector
    /// some z3 operations/apis only work with this vector type, let's keep it
    static z3::expr_vector vec();

    /// return a function expr with a given name, given arguments and given ret type
    static z3::expr packing(const char *, const z3::expr_vector &, unsigned);

    static z3::expr naming(const z3::expr &, const char *);

    static bool is_naming(const z3::expr &);

    static bool is_naming_eq(const z3::expr &);

    /// bv64 -> bv8 byte_array operations
    /// @{
    static z3::expr byte_array();

    static z3::expr byte_array_element(const z3::expr &, int);

    static z3::expr byte_array_element(const z3::expr &, const z3::expr &);

    static z3::expr byte_array_range(const z3::expr &, const z3::expr &, const z3::expr &);

    static bool byte_array_element_index_less_than(const z3::expr &, const z3::expr &);
    /// @}

    /// check if two expr are identical
    /// @{
    static unsigned id(const z3::expr &);

    static bool same(const z3::expr &, const z3::expr &);
    /// @}

    /// check if an expr is numerical
    /// @{
    static bool is_numeral_u64(const z3::expr &, uint64_t &);

    static bool is_numeral_i64(const z3::expr &, int64_t &);

    static bool is_zero(const z3::expr &);
    /// @}

    /// find a set of expr satisfying some conditions
    /// @{
    static bool find(const z3::expr &, const z3::expr &SubExpr);

    static bool find(const z3::expr &, bool (*P)(const z3::expr &));//recursively find expr satisfy P or not

    static bool find_byte_index(const z3::expr &, int (*P)(const z3::expr &));//stop BFS when reach a B[..]

    static z3::expr_vector find_all(const z3::expr &, bool Recursive, bool (*P)(const z3::expr &));

    static z3::expr_vector find_all(const z3::expr_vector &, bool (*P)(const z3::expr &));//given a expr vector V, return a expr vector which contains all the expr in V satisfied P

    static z3::expr_vector find_consecutive_ops(const z3::expr &, bool (*P)(const z3::expr &), bool AllowRep = false);

    static z3::expr_vector find_consecutive_ops(const z3::expr &, Z3_decl_kind, bool AllowRep = false);

    static z3::expr_vector find_consecutive_ops(const z3::expr &, const char *, bool AllowRep = false);

    /// expr to string
    static std::string to_string(const z3::expr &, bool Easy = true);

    /// z3 cast operations, see Z3Cast.cpp
    /// @{
    static z3::expr trunc(const z3::expr &, unsigned);

    static z3::expr trunc_expression(const z3::expr &, unsigned);

    static z3::expr zext(const z3::expr &, unsigned);

    static z3::expr sext(const z3::expr &, unsigned);

    static z3::expr bv_to_bool(const z3::expr &);

    static z3::expr bool_to_bv(const z3::expr &, unsigned);
    /// @}

    /// z3 arithmetic operations, see Z3Arithmetic.cpp
    /// @{
    static z3::expr add(const z3::expr &, int);

    static z3::expr add(const z3::expr &, const z3::expr &);

    static z3::expr sub(const z3::expr &, const z3::expr &);

    static z3::expr mul(const z3::expr &, const z3::expr &);

    static z3::expr udiv(const z3::expr &, const z3::expr &);

    static z3::expr sdiv(const z3::expr &, const z3::expr &);

    static z3::expr urem(const z3::expr &, const z3::expr &);

    static z3::expr srem(const z3::expr &, const z3::expr &);

    static z3::expr bvand(const z3::expr &, const z3::expr &);

    static z3::expr bvor(const z3::expr &, const z3::expr &);

    static z3::expr bvxor(const z3::expr &, const z3::expr &);

    static z3::expr shl(const z3::expr &, const z3::expr &);

    static z3::expr lshr(const z3::expr &, const z3::expr &);

    static z3::expr ashr(const z3::expr &, const z3::expr &);

    static z3::expr concat(const z3::expr &, const z3::expr &);

    static z3::expr concat(std::vector<z3::expr> &);

    static z3::expr concat(const z3::expr_vector &);

    static z3::expr extract(const z3::expr &, unsigned, unsigned);

    static z3::expr extract_byte(const z3::expr &, unsigned);

    static z3::expr extract_byte(const z3::expr &, unsigned, unsigned);

    static z3::expr byteswap(const z3::expr &);
    /// @}

    /// z3 relational operations, see Z3Relational.cpp
    /// @{
    static z3::expr slt(const z3::expr &, const z3::expr &);

    static z3::expr sle(const z3::expr &, const z3::expr &);

    static z3::expr sgt(const z3::expr &, const z3::expr &);

    static z3::expr sge(const z3::expr &, const z3::expr &);

    static z3::expr ult(const z3::expr &, const z3::expr &);

    static z3::expr ule(const z3::expr &, const z3::expr &);

    static z3::expr ugt(const z3::expr &, const z3::expr &);

    static z3::expr uge(const z3::expr &, const z3::expr &);

    static z3::expr eq(const z3::expr &, const z3::expr &);

    static z3::expr ne(const z3::expr &, const z3::expr &);

    static bool is_compare(const z3::expr &);
    /// @}

    /// z3 ternary operations, see Z3Ternary.cpp
    /// @{
    static z3::expr ite(const z3::expr &, const z3::expr &, const z3::expr &);

    static z3::expr make_phi(unsigned ID, const z3::expr_vector &, const z3::expr_vector &);

    static z3::expr make_phi(unsigned ID, const z3::expr_vector &);

    static bool is_phi(const z3::expr &);

    static bool same_phi(const z3::expr &, const z3::expr &);

    static unsigned phi_id(const z3::expr &);

    static unsigned phi_cond_id(unsigned PhiID, unsigned K);

    static z3::expr_vector phi_cond(unsigned PhiID);

    static bool has_phi(unsigned PhiID);

    static z3::expr select_phi_arg(unsigned PhiID, unsigned ArgID, const z3::expr &Expr);

    static void bind_phi_id(unsigned PhiID, BasicBlock *, const std::vector<BasicBlock *> &);

    static const std::vector<BasicBlock *> *phi_predecessor_blocks(unsigned PhiID);

    static BasicBlock *phi_block(unsigned PhiID);
    /// @}

    /// z3 logic operations, see Z3Logic.cpp
    /// @{
    static z3::expr make_and(const z3::expr &, const z3::expr &);

    static z3::expr make_and(const z3::expr_vector &);

    static z3::expr make_and(const std::vector<z3::expr> &V);

    static z3::expr make_or(const z3::expr &, const z3::expr &);

    static z3::expr make_or(const z3::expr_vector &);

    static z3::expr make_or(const std::vector<z3::expr> &);

    static z3::expr negation(const z3::expr &);
    /// @}

    /// simplify expr, see Z3Simplify.cpp
    /// @{
    /// basically perform z3::simplify, but with some additional simplification
    static z3::expr simplify(const z3::expr_vector &);

    /// simplify the second expr according to the first and return a simplified second expr
    static z3::expr simplify(const z3::expr &, const z3::expr &);
    /// @}

    /// some checking operations
    static bool is_distinct_or_not_eq(const z3::expr &);

    /// used for std::set, std::map
    struct less_than {
        bool operator()(const z3::expr &E1, const z3::expr &E2) const {
            return Z3::id(E1) < Z3::id(E2);
        }
    };
};

class Z3Solver {
public:
    static void addAssumption(const z3::expr &Assumption);

    static void clearAssumptions();

    static bool check(const z3::expr &, std::vector<uint8_t> &);

    static bool check(const z3::expr &);

    static bool check(const std::vector<z3::expr> &);

    static bool check(const z3::expr_vector &);

    static void getmodel(const z3::expr &,const z3::expr &,const z3::expr &);
};

raw_ostream &operator<<(llvm::raw_ostream &, const Z3::Z3Format &);

raw_ostream &operator<<(llvm::raw_ostream &, const z3::expr &);

#endif //SUPPORT_Z3_H
