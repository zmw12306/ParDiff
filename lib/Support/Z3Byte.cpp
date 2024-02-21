#include "Z3Macro.h"

z3::expr Z3::byte_array() {
    auto &Ctx = Z3::bool_val(true).ctx();
    return {Ctx,
            Z3_mk_const(
                    Ctx,
                    Z3_mk_string_symbol(Ctx, BYTE_ARRAY),
                    Ctx.array_sort(Ctx.bv_sort(64), Ctx.bv_sort(8))
            )
    };
}

z3::expr Z3::byte_array_element(const z3::expr &Array, int Index) {
    assert(Array.is_array());
    return z3::select(Array, Index);
}

z3::expr Z3::byte_array_element(const z3::expr &Array, const z3::expr &Index) {
    assert(Array.is_array());
    assert(Index.is_bv());

    auto IndexBVSz = Index.get_sort().bv_size();
    assert(IndexBVSz <= 64);
    auto RealIndex = IndexBVSz < 64 ? Z3::zext(Index, 64 - IndexBVSz) : Index;
    return z3::select(Array, RealIndex);
}

z3::expr Z3::byte_array_range(const z3::expr &Array, const z3::expr &F, const z3::expr &T) {
    auto IV = Z3::vec();
    IV.push_back(F);
    IV.push_back(T);

    std::vector<z3::sort> SortVec;
    SortVec.push_back(F.get_sort());
    SortVec.push_back(T.get_sort());

    std::string Range(BYTE_ARRAY_RANGE);
    auto RangeFunc = z3::function(Range.c_str(), SortVec.size(), &SortVec[0], SortVec[0]);
    return RangeFunc(IV);
}

static int truncLessThan(const z3::expr_vector &V1, const z3::expr_vector &V2) {
    // 1 - true
    // 0 - false
    // -1 - unknown
    for (auto E: V1){
        dbgs()<<E<<"\n";
    }
    for (auto E: V2){
        dbgs()<<E<<"\n";
    }
    //dbgs()<< "v1: "<<V1<<" and V2: " <<V2<<"\n";
    unsigned Bits2Remove = 0;
    bool flag = false;
    for (auto E: V1) {
        //dbgs()<< "E "<<E<<" E.decl().decl_kind(): "<<E.decl().decl_kind()<<"\n";
        if (E.decl().decl_kind() == Z3_OP_CONCAT) {
            auto Head = E.arg(0);
            // dbgs()<<"Gead: "<<Head<<"\n";
            // dbgs()<<"head decl_kind: "<< Head.decl().decl_kind()<<"\n";
            // dbgs()<<"bv_size: "<<Head.get_sort().bv_size()<<"\n";
            int64_t Const;
            if (Z3::is_numeral_i64(Head, Const) && Const == 0) {
                //dbgs()<<"here1\n";
                Bits2Remove = Head.get_sort().bv_size();
                break;
            } else if (Head.decl().decl_kind() == Z3_OP_EXTRACT && Head.get_sort().bv_size() == 1) {
                // this may be a signed ext
                //dbgs()<<"here2\n";
                unsigned K = 1;
                for (; K < E.num_args() - 1; K++) {
                    if (!Z3::same(Head, E.arg(K))) {
                        break;
                    }
                }
                if (Z3::same(Head.arg(0), E.arg(K))) {
                    Bits2Remove = K;
                    break;
                }
            }
            
        }
    }
    //dbgs()<<"Bits2Remove: "<<Bits2Remove<<"\n";
    if (Bits2Remove == 0)
        return -1;
    unsigned Bits2Preserve = V1[0].get_sort().bv_size() - Bits2Remove;

    auto TruncHeadZero = [Bits2Remove, Bits2Preserve](const z3::expr_vector &V) {
        auto Ret = Z3::vec();
        int64_t Const;
        for (auto E: V) {
            if (Z3::is_numeral_i64(E, Const)) {
                Ret.push_back(Z3::bv_val(Const, Bits2Preserve));
            } else {
                if (E.decl().decl_kind() == Z3_OP_CONCAT) {
                    auto Head = E.arg(0);
                    if (Z3::is_numeral_i64(Head, Const) && Const == 0) {
                        if (Head.get_sort().bv_size() == Bits2Remove) {
                            auto ConcatVec = Z3::vec();
                            for (unsigned K = 1; K < E.num_args(); ++K)
                                ConcatVec.push_back(E.arg(K));
                            Ret.push_back(z3::concat(ConcatVec));
                        } else if (Head.get_sort().bv_size() > Bits2Remove) {
                            auto ConcatVec = Z3::vec();
                            ConcatVec.push_back(Z3::bv_val(0, Head.get_sort().bv_size() - Bits2Remove));
                            for (unsigned K = 1; K < E.num_args(); ++K)
                                ConcatVec.push_back(E.arg(K));
                            Ret.push_back(z3::concat(ConcatVec));
                        } else {
                            break;
                        }
                    } else if (Head.decl().decl_kind() == Z3_OP_EXTRACT && Head.get_sort().bv_size() == 1) {
                        if (Bits2Remove < E.num_args() &&
                            (Z3::same(E.arg(Bits2Remove), Head.arg(0)) || Z3::same(E.arg(Bits2Remove), Head))) {
                            auto ConcatVec = Z3::vec();
                            for (unsigned K = Bits2Remove; K < E.num_args(); ++K)
                                ConcatVec.push_back(E.arg(K));
                            Ret.push_back(z3::concat(ConcatVec));
                        } else {
                            break;
                        }
                    } 
                    else {
                        break;
                    }
                } else {
                    break;
                }
            }
        }
        return Ret;
    };
    auto NV1 = TruncHeadZero(V1);
    if (NV1.size() != V1.size()) return -1;
    auto NV2 = TruncHeadZero(V2);
    if (NV2.size() != V2.size()) return -1;

    // dbgs()<<"NV1: "<<NV1<<"\n";
    // dbgs()<<"NV2: "<<NV2<<"\n";

    auto BvSum = [](const z3::expr_vector &V) {
        // note: z3::sum() does not support bit vector
        assert(V.size() > 0);
        auto Ret = V[0];
        for (unsigned K = 1; K < V.size(); ++K) {
            Ret = Ret + V[K];
        }
        return Ret.simplify();
    };
    auto N1 = BvSum(NV1);
    auto N2 = BvSum(NV2);
    // dbgs()<<"N1: "<<N1<<"\n";
    // dbgs()<<"N2: "<<N2<<"\n";
    return Z3::byte_array_element_index_less_than(N1, N2) ? 1 : 0;
}

bool Z3::byte_array_element_index_less_than(const z3::expr &A, const z3::expr &B) {
   //errs()<<A << " with " << B<<"\n";
    // first try
    auto Res = Z3::ult(A, B);
    if (Res.is_true())
        return true;
    if (Res.is_false())
        return false;

    auto O1Ops = Z3::find_consecutive_ops(A, Z3_OP_BADD, true);
    auto O2Ops = Z3::find_consecutive_ops(B, Z3_OP_BADD, true);

    // move negative items to the other side
    auto MoveNegativeItem = [](z3::expr_vector &O1Ops, z3::expr_vector &O2Ops) {
        for (unsigned I = 0; I < O1Ops.size(); ++I) {
            auto E = O1Ops[I];
            int64_t Const;
            if (E.decl().decl_kind() == Z3_OP_BMUL) {
                assert(E.num_args() == 2);
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

    // expand mul op: 3 * a => a + a + a
    auto ExpandMul = [](z3::expr_vector &Ops) {
        auto Size = Ops.size();
        for (unsigned I = 0; I < Size; ++I) {
            auto E = Ops[I];
            if (E.decl().decl_kind() == Z3_OP_BMUL) {
                assert(E.num_args() == 2);
                int64_t Const = -1;
                auto Op = Z3::bv_val(0, E.get_sort().bv_size()); // just init the expr
                if (Z3::is_numeral_i64(E.arg(0), Const)) {
                    assert(Const > 0);
                    Op = E.arg(1);
                } else if (Z3::is_numeral_i64(E.arg(1), Const) && Const < 0) {
                    assert(Const > 0);
                    Op = E.arg(0);
                }
                if (Const > 0) {
                    Ops.set(I, Op);
                    Const--;
                    while (Const-- > 0) {
                        Ops.push_back(Op);
                    }
                }
            }
        }
    };
    ExpandMul(O1Ops);
    ExpandMul(O2Ops);

    // remove the same items in two sides
    for (unsigned I = 0; I < O1Ops.size(); ++I) {
        auto E1 = O1Ops[I];
        int64_t Const1;
        bool E1Const = Z3::is_numeral_i64(E1, Const1);
        int64_t OldConst1 = Const1;

        bool FoundSame = false;
        for (unsigned J = 0; J < O2Ops.size(); ++J) {
            auto E2 = O2Ops[J];
            int64_t Const2;
            bool E2Const = Z3::is_numeral_i64(E2, Const2);

            if (Z3::same(E1, E2)) {
                // remove E2 from O2Ops
                auto Back2 = O2Ops.back();
                O2Ops.set(J, Back2);
                O2Ops.pop_back();
                FoundSame = true;
                break;
            } else if (E1Const && E2Const) {
                assert(Const1 > 0 && Const2 > 0);
                if (Const1 > Const2) {
                    // remove E2 from O2Ops
                    auto Back2 = O2Ops.back();
                    O2Ops.set(J, Back2);
                    O2Ops.pop_back();

                    Const1 -= Const2;
                } else {
                    assert(Const1 < Const2);
                    FoundSame = true;
                    auto New = Z3::bv_val(Const2 - Const1, E2.get_sort().bv_size());
                    O2Ops.set(J, New);
                    break;
                }
            }
        }
        if (FoundSame) {
            // remove E1 from O1Ops
            auto Back1 = O1Ops.back();
            O1Ops.set(I, Back1);
            O1Ops.pop_back();
            I--;
        } else if (OldConst1 > Const1) {
            auto New = Z3::bv_val(Const1, E1.get_sort().bv_size());
            O1Ops.set(I, New);
        }
    }
  
    bool ext_flag = false;
    for (unsigned I = 0; I < O1Ops.size(); ++I) {
        ext_flag = false;
        auto Ret1 = Z3::vec();
        auto Ret2 = Z3::vec();
        auto E1 = O1Ops[I];
        if (E1.decl().decl_kind() != Z3_OP_CONCAT) {
            continue;
        }
        auto E1_head = E1.arg(0);
        int64_t Const;
        
        if (Z3::is_numeral_i64(E1_head, Const) && Const == 0){
            E1_head = E1.arg(1);
            ext_flag = true;
        }

        if(E1_head.decl().decl_kind() != Z3_OP_EXTRACT || E1_head.get_sort().bv_size() < 1)
            continue;
        bool FoundSame = false;
        //dbgs()<<"E1_head: "<<E1_head<<"\n";

        for (unsigned J = 0; J < O2Ops.size(); ++J) {
            auto E2 = O2Ops[J];
            if (E2.decl().decl_kind() != Z3_OP_CONCAT) {
                continue;
            }
            auto E2_head= E2.arg(0);
            if(ext_flag){
                if(Z3::is_numeral_i64(E2_head, Const) && Const == 0){
                    E2_head = E2.arg(1);
                }
                else{
                    continue;
                }
                
            }
                
            if(Z3::same(E2_head, E1_head)){
                //dbgs()<<"E2_head: "<<E2_head<<"\n";
                auto ConcatVec = Z3::vec();
                if(ext_flag){
                    ConcatVec.push_back(Z3::bv_val(0, E2.arg(0).get_sort().bv_size() + E2_head.get_sort().bv_size()));
                    for (unsigned K =2; K < E2.num_args(); ++K)
                        ConcatVec.push_back(E2.arg(K));
                }
                    
                else{
                    ConcatVec.push_back(Z3::bv_val(0, E2_head.get_sort().bv_size()));
                    for (unsigned K = 1; K < E2.num_args(); ++K)
                        ConcatVec.push_back(E2.arg(K));
                }
                    
                auto X = z3::concat(ConcatVec);
                O2Ops.set(J, X);             
                FoundSame = true;
                break;
            }
        }
        if(FoundSame){
            auto ConcatVec = Z3::vec();
            if(ext_flag){
                ConcatVec.push_back(Z3::bv_val(0, E1.arg(0).get_sort().bv_size() + E1_head.get_sort().bv_size()));
                for (unsigned K =2; K < E1.num_args(); ++K)
                    ConcatVec.push_back(E1.arg(K));
            }
                
            else{
                ConcatVec.push_back(Z3::bv_val(0, E1_head.get_sort().bv_size()));
                for (unsigned K = 1; K < E1.num_args(); ++K)
                    ConcatVec.push_back(E1.arg(K));
            }
            auto Y = z3::concat(ConcatVec);
            O1Ops.set(I, Y);   
            auto BvSum = [](const z3::expr_vector &V) {
        // note: z3::sum() does not support bit vector
                assert(V.size() > 0);
                auto Ret = V[0];
                for (unsigned K = 1; K < V.size(); ++K) {
                    Ret = Ret + V[K];
                }
                return Ret.simplify();
            };
            auto N1 = BvSum(O1Ops);
            auto N2 = BvSum(O2Ops);
            // dbgs()<<"O1OpsNN1: "<<N1<<"\n";
            // dbgs()<<"O2OpsNN2: "<<N2<<"\n";
            return Z3::byte_array_element_index_less_than(N1, N2) ? 1 : 0;               
        }
    }


    if (O1Ops.empty() && !O2Ops.empty()) {
        //errs()<<A << " < " << B << " yields true!\n";
        LLVM_DEBUG(dbgs() << A << " < " << B << " yields true!\n");
        return true;
    } else if (!O1Ops.empty() && O2Ops.empty()) {
        //errs()<< A << " < " << B << " yields false (>)!\n";
        LLVM_DEBUG(dbgs() << A << " < " << B << " yields false (>)!\n");
        return false;
    } else if (O1Ops.empty() && O2Ops.empty()) {
        //errs()<< A << " < " << B << " yields false (=)!\n";
        LLVM_DEBUG(dbgs() << A << " < " << B << " yields false (=)!\n");
        return false;
    } else {
        int64_t Const;
        if (O1Ops.size() == 1 && Z3::is_numeral_i64(O1Ops[0], Const)) {
            //errs()<< A << " < " << B << " yields true (*)!\n";
            LLVM_DEBUG(dbgs() << A << " < " << B << " yields true (*)!\n");
            return true;
        } else if (O2Ops.size() == 1 && Z3::is_numeral_i64(O2Ops[0], Const)) {
            //errs()<< A << " < " << B << " yields false (*)!\n";
            LLVM_DEBUG(dbgs() << A << " < " << B << " yields false (*)!\n");
            return false;
        } else {
            auto Ret = truncLessThan(O1Ops, O2Ops);
            //dbgs()<<":ret1"<< Ret<<"\n";
            if (Ret != -1) {
                //errs()<<A << " < " << B << " yields " << Ret << " (*)!\n";
                LLVM_DEBUG(dbgs() << A << " < " << B << " yields " << Ret << " (*)!\n");
                return Ret;
            } else {
                Ret = truncLessThan(O2Ops, O1Ops);
                //dbgs()<<":ret2"<< Ret<<"\n";
                if (Ret != -1) {
                    //errs()<<A << " < " << B << " yields " << Ret << " (*)!ha\n";
                    LLVM_DEBUG(dbgs() << A << " < " << B << " yields " << !Ret << " (*)!\n");
                    return Ret == 0 ? 1 : 0;
                }
            }
        }
        return 1;
        LLVM_DEBUG(
                dbgs() << A << " < " << B << "\n-----\nO1Ops: \n";
                dbgs() <<"O1Ops.size(): "<<O1Ops.size()<<"\n";
                dbgs() <<Z3::is_numeral_i64(O1Ops[0], Const)<<"\n";

                dbgs()<<"O2Ops.size(): "<<O2Ops.size()<<"\n";
                dbgs() <<Z3::is_numeral_i64(O2Ops[0], Const)<<"\n";
                dbgs()<<"rest= "<<truncLessThan(O1Ops, O2Ops)<<"\n";

                for (auto X: O1Ops) dbgs() << X << ", ";
                dbgs() << "\n-----\nO2Ops: \n";
                for (auto X: O2Ops) dbgs() << X << ", ";
                dbgs() << "\n-----\n"
        );
        // dbgs() << A << " < " << B << "\n-----\nO1Ops: \n";
        // dbgs() <<"O1Ops.size(): "<<O1Ops.size()<<"\n";
        // dbgs() <<Z3::is_numeral_i64(O1Ops[0], Const)<<"\n";

        // dbgs()<<"O2Ops.size(): "<<O2Ops.size()<<"\n";
        // dbgs() <<Z3::is_numeral_i64(O2Ops[0], Const)<<"\n";
        // dbgs()<<"rest= "<<truncLessThan(O1Ops, O2Ops)<<"\n";

        // for (auto X: O1Ops) dbgs() << X << ", ";
        // dbgs() << "\n-----\nO2Ops: \n";
        // for (auto X: O2Ops) dbgs() << X << ", ";
        // dbgs() << "\n-----\n";

        std::string ErrMsg;
        raw_string_ostream Str(ErrMsg);
        Str << "Error: not comparable...\n\n";
        Str << A << " < " << B << "\n-----\nO1Ops: \n";
        for (auto X: O1Ops) Str << X << ", ";
        Str << "\n-----\nO2Ops: \n";
        for (auto X: O2Ops) Str << X << ", ";
        Str << "\n-----\n";
        Str.flush();
        throw std::runtime_error(ErrMsg);
    }
}