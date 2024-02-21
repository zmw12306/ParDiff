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

#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/Debug.h>
#include <list>
#include <set>
#include "Core/Executor.h"
#include "Support/Debug.h"
#include "Support/DL.h"
#include "Support/TimeRecorder.h"

#define DEBUG_TYPE "Executor"
#define UNKNOWN_NAME "unknown"

static cl::opt<bool> EnableRecursiveCall(
        "pardiff-enable-recursive-call",
        cl::desc("enable recursive call"),
        cl::init(false));
static cl::opt<bool> LengthSolution(
        "pardiff-enable-length-solution",
        cl::desc("enable length solution"),
        cl::init(true));
static cl::opt<std::string> DebugL2CAPChannel(
        "pardiff-debug-l2cap",
        cl::desc("works only with -debug-only=L2CAP, possible values include:"
                 "l2cap_sig_channel, l2cap_data_channel, l2cap_le_sig_channel, and l2cap_conless_channel"),
        cl::init(""));
static cl::opt<std::string> DebugSSQChannel(
        "pardiff-debug-ssq",
        cl::desc("works only with -debug-only=SSQ, possible values include:"
                 "ssq_info_deserialize, ssq_player_deserialize, ssq_rules_deserialize"),
        cl::init(""));
static cl::opt<unsigned> DebugSrcLine(
        "pardiff-debug-line",
        cl::desc("allows we set break point at some place"),
        cl::init(0), cl::ReallyHidden);
static cl::opt<bool> AssertionPacking(
        "pardiff-enable-assert-packing",
        cl::desc("packing complex assertions into a single predicate"),
        cl::init(false));
static cl::opt<bool> UseGlobal(
        "pardiff-enable-global",
        cl::desc("using global variables"),
        cl::init(false));
static cl::opt<bool> EnableNaming(
        "pardiff-enable-naming",
        cl::desc("inferring field"),
        cl::init(false));

#ifndef NDEBUG
static std::map<Value *, unsigned> ValueCounter;

static unsigned getCounter(Value *V) {
    assert(isa<Instruction>(V) || isa<Function>(V));
    unsigned Ret = 0;
    auto It = ValueCounter.find(V);
    if (It != ValueCounter.end())
        Ret = It->second;
    return Ret;
}

static void setCounter(Value *V) {
    assert(isa<Instruction>(V) || isa<Function>(V));
    auto It = ValueCounter.find(V);
    if (It != ValueCounter.end()) {
        It->second++;
        return;
    }
    ValueCounter[V] = 0;
}

static std::string space(unsigned N) {
    std::string Ret;
    while (N-- > 0) {
        Ret.append(" ");
    }
    return Ret;
}

#define DEBUG_FUNC(FUNC_PTR, X)                                             \
    do {                                                                    \
       X;                                                              \
    } while (false)
// #define DEBUG_FUNC(FUNC_PTR, X)                                             \
    // do {                                                                    \
    //     if (::llvm::DebugFlag) {                                            \
    //         if (::llvm::isCurrentDebugType(DEBUG_TYPE)) {X; break;}         \
    //         std::string TYPE((FUNC_PTR)->getName().str());                  \
    //         TYPE.append("@").append(std::to_string(getCounter(FUNC_PTR)));  \
    //         if (::llvm::isCurrentDebugType(TYPE.c_str())) {X;}              \
    //     }                                                                   \
    // } while (false)

#else
#define space(X) ""
#define setCounter(X)
#define getCounter(X) 123
#define DEBUG_FUNC(FUNC_PTR, X)
#endif

//static MemoryBlock *WhereDataStored = nullptr;

static std::set<std::string> ByteSwapFunctions = {
        "htonll", "htonl", "htons", "ntohll", "ntohl", "ntohs","ip_masklen"
};

static std::set<std::string> DeadFunctions = {
        "gettime","linklocal","update_neighbour_metric","find_neighbour","send_challenge_request","bgp_conn_enter_established_state","bgp_update_implicit_eors","sockopt_tcp_rtt",
        "neighbour_rxcost","find_neighbour_nocreate","update_neighbour","flush_neighbour","local_notify_neighbour","reset_txcost","neighbour_txcost", "bgp_notify_send",
        "check_neighbours","neighbour_rxcost","neighbour_rttcost","neighbour_cost","schedule_neighbours_check","timeval_compare","neigh_find","handle_request",
        "l2cap_build_cmd", "l2cap_chan_close", "l2cap_raw_recv","compare_hmac","atomic_fetch_add_explicit","bgp_stop","bgp_error","ea__find","bgp_decode_attr","atomic_fetch_add_explicit","hook_call",
        "osdp_compute_mac", "osdp_compute_crc16", "osdp_get_rand","SHA256Reset","bgp_schedule_packet","bgp_update_startup_delay","bgp_update","bgp_decode_nlri",
        "isis_unpack_tlvs", "isis_te_lsp_event", "ack_lsp", "isis_adj_build_neigh_list", "isis_tlvs_to_adj","ptm_bfd_sess_find","bs_state_handler","ipa_in_netX","rip_peer_bad_packet","ripng_peer_bad_packet","rip_update_rte","ripng_peer_update","rip_withdraw_rte","ip_masklen","password_find_by_value","password_find_by_id",
        "ospf_if_lookup_recv_if","ospf_neighbor_new","ospf_check_and_gen_init_seq_lsa","ospf_ls_retransmit_lookup","ospf_ls_retransmit_delete","ospf6_lsdb_add","ICMP6_STATS_INC"//,"ospf_nbr_bidirectional"
};

static std::set<std::string> DeadFunctionStartsWith = {
        "ngtcp2_ksl_", // quic
        "zlog_", // babel, isis
        "lsp_", "yang_data_", "listnode_", "neighbour_", "SHA", "SHA224_","blake2","bgp_conn_","fib_","ev_","rte_",//"ip6_","ip4_", // isis
        "lsa_","ospf_lsdb_","ospf_lsa_","ospf_enqueue_","rip_auth_","ospf6_lstype_","ospf6_lsdb_","ospf6_lsa_","bgp_decode","peek_for_as4","__IP6_ADD_STATS"
};

static std::set<std::string> DeadFunctionContains = {
     "table", "lookup", "lookfor", "hash","hmac","log","mac","afi","safi","peer","error","timer","prefix",
    "send", "output", "route", "debug","resend","frrtrace","trace","session",
        "release", "free", "realloc","SHA", "blake2","time","format","dump","channel",//"ipsum_verify",
         "md5", "print", "thread","neighbour","alloc","neigh","hash"//"ip6","ip4",
};//"hmac","auth", "chksum", "csum","checksum"
static bool isDeadFunction(Function *F) {
    auto LCCalleeName = F->getName().lower();
    StringRef CalleeName(LCCalleeName);

    for (auto &Str: DeadFunctionContains) {
        if (CalleeName.contains(Str)) return true;
    }

    for (auto &Str: DeadFunctionStartsWith) {
        if (CalleeName.startswith(Str)) return true;
    }

    return DeadFunctions.count(LCCalleeName);
}

static bool isByteSeq(const z3::expr &Expr, z3::expr_vector *Vec = nullptr) {
    auto UnfoldExpr = Expr;
    if (Expr.decl().decl_kind() == Z3_OP_ZERO_EXT || Expr.decl().decl_kind() == Z3_OP_SIGN_EXT) {
        UnfoldExpr = Expr.arg(0);
    }
    if (UnfoldExpr.decl().decl_kind() == Z3_OP_SELECT) {
        if (Vec) Vec->push_back(UnfoldExpr);
        return true;
    }
    if (UnfoldExpr.decl().decl_kind() != Z3_OP_CONCAT) return false;

    bool HasByte = false;
    bool AllBytesOrConstant = true;
    uint64_t Const;
    for (unsigned K = 0; K < UnfoldExpr.num_args(); ++K) {
        auto E = UnfoldExpr.arg(K);
        auto EID = Z3::id(E);
        if (E.decl().decl_kind() == Z3_OP_SELECT) {
            HasByte = true;
            if (Vec) Vec->push_back(E);
        } else if (Z3::is_numeral_u64(E, Const)) {
            // do nothing
        } else {
            AllBytesOrConstant = false;
            break;
        }
    }
    return HasByte && AllBytesOrConstant;
}

unsigned Executor::MergeID = 0;
unsigned Executor::LoopAnalysisID = 0;
std::map<Value *, DIType *> Executor::ValueDebugTypeMap;

void Executor::visitBr(BranchInst &I) {
}

void Executor::visitSwitch(SwitchInst &I) {
}

void Executor::visitIndirectBr(IndirectBrInst &I) {
    // This is typically implemented with a jump through a register, meaning inline asm,
    // thus regarding it as a branch with unknown condition
}

void Executor::visitCallBr(CallBrInst &I) {
    // This is only used for inline asm, thus regarding it as a branch with unknown condition
}

void Executor::visitPHI(PHINode &I) {
    inferDITypePHI(I);

    auto *AV = ES->registerAllocate(&I);
    if (auto *LP = FLI->isLoopHeader(I.getParent())) {
        bool FromPreHead = LastProcessingBlockPointer < ProcessingBlockPointer;

        assert(I.getNumIncomingValues() == 2);
        for (unsigned K = 0; K < 2; ++K) {
            auto *IncomingBlock = I.getIncomingBlock(K);
            if (FromPreHead) {
                // skip the value from the latch
                if (FLI->isLoopLatch(IncomingBlock) == LP) {
                    continue;
                }
            } else {
                // skip the value from the prehead
                if (FLI->isLoopLatch(IncomingBlock) != LP) {
                    continue;
                }
            }

            auto *IncomingVal = I.getIncomingValue(K);
            auto *IncomingAV = ES->boundValue(IncomingVal);
            AV->assign(IncomingAV);
        }
        if (!isa<PHINode>(I.getNextNode())) {
            for (auto *BlockInLoop: *LP)
                for (auto &InstInLoop: *BlockInLoop) {
                    if (InstInLoop.getType()->isVoidTy()) continue;
                    if (InstInLoop.getParent() != I.getParent() || !isa<PHINode>(InstInLoop))
                        ES->registerDeallocate(&InstInLoop);
                }
        }
        return;
    }

    z3::expr_vector AVVec = Z3::vec();
    z3::expr_vector CondVec = Z3::vec();
    bool AllPoison = true;
    for (unsigned K = 0; K < I.getNumIncomingValues(); ++K) {
        auto MergeCond = MergeCondMap[I.getParent()][K];
        if (MergeCond.is_false())
            continue;

        auto *IncomingVal = I.getIncomingValue(K);
        auto *IncomingAV = ES->boundValue(IncomingVal);
        if (!IncomingAV->poison() && AllPoison) AllPoison = false;
        if (isa<AddressValue>(IncomingAV)) {
            AV->add(IncomingAV);
        } else {
            AVVec.push_back(IncomingAV->poison() ? Z3::free_bv(IncomingAV->bytewidth() * 8) : IncomingAV->value());
            CondVec.push_back(MergeCond);
        }
    }
    if (!AllPoison && !AVVec.empty()) {
        // llvm::slice_Inst.insert(&I);
        AV->set(Z3::make_phi(MergeID, AVVec, CondVec));
    }
    if (!isa<PHINode>(I.getNextNode())) MergeCondMap.erase(I.getParent());
}

void Executor::visitCall(CallInst &I) {
    //llvm::slice_Inst.insert(&I);
    Function *Callee = I.getCalledFunction();
    if (Callee && Callee->empty()) {
        switch (Callee->getIntrinsicID()) {
            case Intrinsic::memcpy_element_unordered_atomic:
            case Intrinsic::memcpy:
                visitMemCpy(I);
                break;
            case Intrinsic::memset_element_unordered_atomic:
            case Intrinsic::memset:
                visitMemSet(I);
                break;
            case Intrinsic::memmove_element_unordered_atomic:
            case Intrinsic::memmove:
                visitMemMov(I);
                break;
            case Intrinsic::bswap:
                visitByteSwap(I);
                break;
            case Intrinsic::is_constant:
                visitIsConstant(I);
                break;
            case Intrinsic::dbg_value:
                visitDbgValue((DbgValueInst &) I);
                break;
            case Intrinsic::dbg_declare:
                visitDbgDeclare((DbgDeclareInst &) I);
                break;
            case Intrinsic::dbg_addr:
            case Intrinsic::dbg_label:
            default:
                StringRef CalleeName = Callee->getName();
                if (CalleeName == "__memcpy_chk") {
                    visitMemCpy(I);
                } else if (CalleeName == "__memset_chk") {
                    visitMemSet(I);
                } else if (CalleeName == "pardiff_make_message") {
                    visitpardiffMakeMessage(I);
                } else if (CalleeName == "pardiff_make_message_length") {
                    visitpardiffMakeMessageLen(I);
                } else if (CalleeName == "calloc") {
                    visitCalloc(I);
                } else if (CalleeName == "malloc" || CalleeName == "pardiff_make_object") {
                    visitMalloc(I);
                } else if (CalleeName == "pardiff_make_named_object") {
                    visitpardiffMakeNamedObject(I);
                } else if (ByteSwapFunctions.count(CalleeName.str())) {
                    visitByteSwap(I);
                } else if (CalleeName == "memcmp") {
                    visitMemCmp(I);
                } else if (CalleeName == "strncmp") {
                    visitStrNCmp(I);
                } else if (CalleeName == "strcmp") {
                    visitStrCmp(I);
                } else {
                    visitCallDefault(I);
                }
                break;
        }
    } else if (!Callee) {
        visitCallDefault(I);
    } else {
        if (isDeadFunction(Callee)) {
            visitCallDefault(I);
        } else if (Callee->getName() == "ssq_buf_strlen") {
            visitSSQBufStrLen(I);
        } else {
            assert(!Callee->empty());
            visitCallIPA(I);
        }
    }
}

void Executor::visitVAArg(VAArgInst &I) {
    // we do not support virtual register returned by the va_arg inst
    // because we observe that such operations are usually not related
    ES->registerAllocate(&I);
    // auto x = ES->boundValue(&I);
    // if(x && !x->poison())
    //     llvm::slice_Inst.insert(&I); 
}

void Executor::visitInvoke(InvokeInst &I) {
    errs() << I << "\n";
    llvm_unreachable("Error: lower-invoke fails or not C code!");
}

void Executor::visitResume(ResumeInst &I) {
    errs() << I << "\n";
    llvm_unreachable("Error: lower-invoke fails or not C code!");
}

void Executor::visitUnreachable(UnreachableInst &I) {
    // do nothing
}

void Executor::visitCleanupRet(CleanupReturnInst &I) {
    errs() << I << "\n";
    llvm_unreachable("Error: lower-invoke fails or not C code!");
}

void Executor::visitCatchRet(CatchReturnInst &I) {
    errs() << I << "\n";
    llvm_unreachable("Error: lower-invoke fails or not C code!");
}

void Executor::visitCatchSwitch(CatchSwitchInst &I) {
    errs() << I << "\n";
    llvm_unreachable("Error: lower-invoke fails or not C code!");
}

void Executor::visitFNeg(UnaryOperator &I) {
    auto *P = ES->boundValue(I.getOperand(0));
    assert(P);
    // if(!P->poison())
    //     llvm::slice_Inst.insert(&I);
    abs_value::neg(ES->registerAllocate(&I), P);
}

#define BINARY_OP_IMPL(OP) {                           \
        auto *Op1 = I.getOperand(0);                   \
        auto *Op2 = I.getOperand(1);                   \
        auto *P1 = ES->boundValue(I.getOperand(0));    \
        auto *P2 = ES->boundValue(I.getOperand(1));    \
        assert(P1 && P2);                              \
        auto *Result = ES->registerAllocate(&I);       \
        OP(Result, P1, P2);                            \
        }

void Executor::visitAdd(BinaryOperator &I) BINARY_OP_IMPL(abs_value::add)

void Executor::visitFAdd(BinaryOperator &I) BINARY_OP_IMPL(abs_value::add)

void Executor::visitSub(BinaryOperator &I) BINARY_OP_IMPL(abs_value::sub)

void Executor::visitFSub(BinaryOperator &I) BINARY_OP_IMPL(abs_value::sub)

void Executor::visitMul(BinaryOperator &I) BINARY_OP_IMPL(abs_value::mul)

void Executor::visitFMul(BinaryOperator &I) BINARY_OP_IMPL(abs_value::mul)

void Executor::visitUDiv(BinaryOperator &I) BINARY_OP_IMPL(abs_value::udiv)

void Executor::visitSDiv(BinaryOperator &I) BINARY_OP_IMPL(abs_value::sdiv)

void Executor::visitFDiv(BinaryOperator &I) BINARY_OP_IMPL(abs_value::sdiv)

void Executor::visitURem(BinaryOperator &I) BINARY_OP_IMPL(abs_value::urem)

void Executor::visitSRem(BinaryOperator &I) BINARY_OP_IMPL(abs_value::sdiv)

void Executor::visitFRem(BinaryOperator &I) BINARY_OP_IMPL(abs_value::srem)

void Executor::visitShl(BinaryOperator &I) BINARY_OP_IMPL(abs_value::shl)

void Executor::visitLShr(BinaryOperator &I) BINARY_OP_IMPL(abs_value::lshr)

void Executor::visitAShr(BinaryOperator &I) BINARY_OP_IMPL(abs_value::ashr)

void Executor::visitAnd(BinaryOperator &I) BINARY_OP_IMPL(abs_value::bvand)

void Executor::visitOr(BinaryOperator &I) BINARY_OP_IMPL(abs_value::bvor)

void Executor::visitXor(BinaryOperator &I) {
    auto *Op1 = I.getOperand(0);
    auto *Op2 = I.getOperand(1);
    auto *P1 = ES->boundValue(I.getOperand(0));
    auto *P2 = ES->boundValue(I.getOperand(1));
    assert(P1 && P2);
    auto *Result = ES->registerAllocate(&I);

    if (I.getType()->isIntegerTy(1)) {
        // e.g., %lnot = xor i1 %cmp, true
        if (P1->poison() || P2->poison()) return;
        auto E1 = P1->value();
        auto E2 = P2->value();
        if (E1.is_ite() && E2.is_ite()) {
            if (Z3::same(E1.arg(1), E2.arg(1)) && Z3::same(E1.arg(2), E2.arg(2))) {
                auto ResExpr = Z3::ne(E1.arg(0), E2.arg(0));
                Result->set(Z3::bool_to_bv(ResExpr, Result->bytewidth() * 8));
                return;
            } else if (Z3::same(E1.arg(1), E2.arg(2)) && Z3::same(E1.arg(2), E2.arg(1))) {
                auto ResExpr = Z3::eq(E1.arg(0), E2.arg(0));
                Result->set(Z3::bool_to_bv(ResExpr, Result->bytewidth() * 8));
                return;
            }
        }
        auto ResExpr = Z3::ne(E1, E2);
        Result->set(Z3::bool_to_bv(ResExpr, Result->bytewidth() * 8));
        return;
    }
    // if(!Result->poison()) 
    //     llvm::slice_Inst.insert(&I); 
    abs_value::bvxor(Result, P1, P2);
}

void Executor::visitICmp(ICmpInst &I) {
    if (I.getOperand(0)->getType()->isPointerTy()) {
        auto *Op1 = I.getOperand(0);
        auto *Op2 = I.getOperand(1);
        auto *P1 = ES->boundValue(I.getOperand(0));
        auto *P2 = ES->boundValue(I.getOperand(1));
        assert(P1 && P2);
        auto *Result = ES->registerAllocate(&I);
        if (I.getPredicate() == CmpInst::ICMP_EQ) {
            if (isa<ConstantPointerNull>(Op1) && P2->size() == 1) {
                if (P2->base(0)) {
                    Result->set(Z3::bv_val(0, Result->bytewidth() * 8));
                } else {
                    Result->set(Z3::bv_val(1, Result->bytewidth() * 8));
                }
            } else if (isa<ConstantPointerNull>(Op2) && P1->size() == 1) {
                if (P1->base(0)) {
                    Result->set(Z3::bv_val(0, Result->bytewidth() * 8));
                } else {
                    Result->set(Z3::bv_val(1, Result->bytewidth() * 8));
                }
            }
        } else if (I.getPredicate() == CmpInst::ICMP_NE) {
            if (isa<ConstantPointerNull>(Op1) && P2->size() == 1) {
                if (P2->base(0)) {
                    Result->set(Z3::bv_val(1, Result->bytewidth() * 8));
                } else {
                    Result->set(Z3::bv_val(0, Result->bytewidth() * 8));
                }
            } else if (isa<ConstantPointerNull>(Op2) && P1->size() == 1) {
                if (P1->base(0)) {
                    Result->set(Z3::bv_val(1, Result->bytewidth() * 8));
                } else {
                    Result->set(Z3::bv_val(0, Result->bytewidth() * 8));
                }
            }
        }
        // for flow sensitive analysis, we do not care about
        // the result of comparing two addresses
        // if(!Result->poison()) 
        //     llvm::slice_Inst.insert(&I); 
        return;
    } else if (compareLength(&I)) {
        return;
    }

    switch (I.getPredicate()) {
        case CmpInst::ICMP_EQ: BINARY_OP_IMPL(abs_value::eq)
            break;
        case CmpInst::ICMP_NE: BINARY_OP_IMPL(abs_value::ne)
            break;
        case CmpInst::ICMP_UGT: BINARY_OP_IMPL(abs_value::ugt)
            break;
        case CmpInst::ICMP_UGE: BINARY_OP_IMPL(abs_value::uge)
            break;
        case CmpInst::ICMP_ULT: BINARY_OP_IMPL(abs_value::ult)
            break;
        case CmpInst::ICMP_ULE: BINARY_OP_IMPL(abs_value::ule)
            break;
        case CmpInst::ICMP_SGT: BINARY_OP_IMPL(abs_value::sgt)
            break;
        case CmpInst::ICMP_SGE: BINARY_OP_IMPL(abs_value::sge)
            break;
        case CmpInst::ICMP_SLT: BINARY_OP_IMPL(abs_value::slt)
            break;
        case CmpInst::ICMP_SLE: BINARY_OP_IMPL(abs_value::sle)
            break;
        default:
            llvm_unreachable("Error: wrong predicate for cmp!");
    }
}

void Executor::visitFCmp(FCmpInst &I) {
    //assert(I.getType()->isFloatingPointTy());
    switch (I.getPredicate()) {
        case CmpInst::FCMP_UEQ:
        case CmpInst::FCMP_OEQ: BINARY_OP_IMPL(abs_value::eq)
            break;
        case CmpInst::FCMP_UGT:
        case CmpInst::FCMP_OGT: BINARY_OP_IMPL(abs_value::sgt)
            break;
        case CmpInst::FCMP_UGE:
        case CmpInst::FCMP_OGE: BINARY_OP_IMPL(abs_value::sge)
            break;
        case CmpInst::FCMP_ULT:
        case CmpInst::FCMP_OLT: BINARY_OP_IMPL(abs_value::slt)
            break;
        case CmpInst::FCMP_ULE:
        case CmpInst::FCMP_OLE: BINARY_OP_IMPL(abs_value::sle)
            break;
        case CmpInst::FCMP_UNE:
        case CmpInst::FCMP_ONE: BINARY_OP_IMPL(abs_value::ne)
            break;
        case CmpInst::FCMP_ORD:
        case CmpInst::FCMP_UNO:{
            ES->registerAllocate(&I);
            //auto x = ES->boundValue(&I);
            // if(!(ES->boundValue(&I)->poison()))
            //     llvm::slice_Inst.insert(&I); 
           
        }
            break;
        case CmpInst::FCMP_TRUE: {
            auto *Result = ES->registerAllocate(&I);
            Result->set(Z3::bv_val(1, Result->bytewidth() * 8));
            // if(!Result->poison()) 
            //     llvm::slice_Inst.insert(&I); 
        }
            break;
        case CmpInst::FCMP_FALSE: {

            auto *Result = ES->registerAllocate(&I);
            Result->set(Z3::bv_val(0, Result->bytewidth() * 8));
            // if(!Result->poison()) 
            //     llvm::slice_Inst.insert(&I); 
        }
            break;
        default:
            llvm_unreachable("Error: wrong predicate for cmp!");
    }
}

void Executor::visitSelect(SelectInst &I) {
    inferDITypeSelect(I);
    if (I.getType()->isPointerTy()) {
        auto *Cond = I.getOperand(0);
        auto *Op1 = I.getOperand(1);
        auto *Op2 = I.getOperand(2);

        auto *C = cast_or_null<ScalarValue>(ES->boundValue(Cond));
        assert(C && "Condition cannot be constant, otherwise why we need select!");
        auto *P1 = cast_or_null<AddressValue>(ES->boundValue(Op1));
        auto *P2 = cast_or_null<AddressValue>(ES->boundValue(Op2));
        assert(P1 && P2);
        auto *Result = cast<AddressValue>(ES->registerAllocate(&I));
        Result->add(P1);
        Result->add(P2);
        // if(!Result->poison()) 
        //     llvm::slice_Inst.insert(&I); 
    } else {
        errs() << I << "\n";
        llvm_unreachable("Error: lower-select fails!");
    }  
}

void Executor::visitAlloca(AllocaInst &I) {
    auto *NumVal = I.getArraySize();
    int64_t Num = 1;
    if (auto CI = dyn_cast<ConstantInt>(NumVal)) {
        Num = CI->getSExtValue();
        if (Num <= 0) Num = 1;
    }
    alloc(MemoryBlock::MK_Stack, &I, I.getAllocatedType(), Num);
}

void Executor::visitLoad(LoadInst &I) {
    inferDITypeLoad(I);

    auto *ResultVal = ES->registerAllocate(&I);
    if (!I.getType()->isSingleValueType()) {
        return;
    }

    auto *AddrVal = cast<AddressValue>(ES->boundValue(I.getPointerOperand()));
    load(&I, AddrVal, ResultVal);
    // if(!ResultVal->poison()) 
    //     llvm::slice_Inst.insert(&I); 
}

void Executor::visitStore(StoreInst &I) {
    auto *Where2Store = I.getPointerOperand();
    auto *Value2Store = I.getValueOperand();

    auto *AddrVal = cast<AddressValue>(ES->boundValue(Where2Store));
    auto *Val2St = ES->boundValue(Value2Store);
    store(&I, AddrVal, Val2St);
    // if(!AddrVal->poison() && !Val2St->poison())
    //    llvm::slice_Inst.insert(&I); 
//    if (!WhereDataStored && isa<AddressValue>(Val2St) && Val2St->size() == 1 && isa<MessageBuffer>(Val2St->base(0))) {
//        WhereDataStored = AddrVal->base(0);
//        unsigned Offset = 0;
//        while (true) {
//            auto *X = ES->getValue(WhereDataStored->at(Offset), false);
//            if (!X) break;
//            Offset += X->bytewidth();
//            outs() << X->str() << "\n";
//        }
//        outs() << "";
//    }

    if (!EnableNaming) return;

    z3::expr_vector Bytes2Name = Z3::vec();
    if (auto *Global = dyn_cast<GlobalVariable>(Where2Store)) {
        auto *GlobalDbg = Global->getMetadata("dbg");
        if (auto *GlobalVarExp = dyn_cast_or_null<DIGlobalVariableExpression>(GlobalDbg)) {
            if (!GlobalVarExp->getExpression()->getNumElements()) {
                // this is like pointer type cast
                naming(I.getFunction(), I.getValueOperand(), GlobalVarExp->getVariable());
            }
        }
    } else if (isa<ScalarValue>(Val2St) && !Val2St->poison()
               && getBytes2Name(Val2St->value(), Bytes2Name) && !Bytes2Name.empty()) {
        auto FieldName = getStructFieldName(Where2Store);
        if (FieldName != UNKNOWN_NAME) {
            for (auto B: Bytes2Name) ES->addPC(Z3::naming(B, FieldName.c_str()));
        }
    }
}

void Executor::visitGetElementPtr(GetElementPtrInst &I) {
    inferDITypeGEP(I);

    auto *ResultVal = cast<AddressValue>(ES->registerAllocate(&I));
    auto *AddrVal = ES->boundValue(I.getPointerOperand());
    assert(AddrVal);
    ResultVal->assign(cast<AddressValue>(AddrVal)); // initialize the resulting address

    // iterate the gep inst
    Type *CurrTy = I.getPointerOperandType();
    Type *CurrTyElmtTy = nullptr;
    if (CurrTy->isPointerTy())
        CurrTyElmtTy = CurrTy->getPointerElementType();
    else if (CurrTy->isArrayTy())
        CurrTyElmtTy = CurrTy->getArrayElementType();

    for (auto It = I.idx_begin(), E = I.idx_end(); It != E; ++It) {
        Value *IndexVal = It->get();
        int64_t Idx = -1;

        if (auto CI = dyn_cast<ConstantInt>(IndexVal)) {
            Idx = CI->getSExtValue();
            if (Idx >= 0) {
                if (CurrTyElmtTy) {
                    ResultVal->forward(Idx * DL::getNumBytes(CurrTyElmtTy));
                } else {
                    assert(isa<StructType>(CurrTy));
                    auto *SL = DL::getStructLayout(CurrTy);
                    ResultVal->forward(SL->getElementOffset(Idx));
                }
            } else {
                ResultVal->mkpoison();
                break;
            }
        } else {
            assert(CurrTyElmtTy && "must be a pointer/array ty!");
            auto *IV = cast<ScalarValue>(ES->boundValue(IndexVal));
            auto ElementSz = DL::getNumBytes(CurrTyElmtTy);
            ResultVal->forward(IV, ElementSz);

            // we may issue some pc here
            uint64_t X;
            if (CurrTy->isArrayTy() && !IV->poison() && !IV->uint64(X)) {
                auto Inbound = Z3::uge(IV->value(), Z3::bv_val(0, IV->bytewidth() * 8)) &&
                               Z3::ult(IV->value(), Z3::bv_val(CurrTy->getArrayNumElements(), IV->bytewidth() * 8));
                ES->addPC(Inbound.simplify());
            }
        }

        // update type
        if (CurrTy->isPointerTy()) {
            CurrTy = CurrTy->getPointerElementType();
        } else if (CurrTy->isArrayTy()) {
            CurrTy = CurrTy->getArrayElementType();
        } else if (CurrTy->isStructTy()) {
            CurrTy = CurrTy->getStructElementType(Idx);
        }
        if (CurrTy->isPointerTy()) {
            CurrTyElmtTy = CurrTy->getPointerElementType();
        } else if (CurrTy->isArrayTy()) {
            CurrTyElmtTy = CurrTy->getArrayElementType();
        } else if (CurrTy->isStructTy()) {
            CurrTyElmtTy = nullptr;
        }
    }
    // if(!ResultVal->poison()) 
    //     llvm::slice_Inst.insert(&I); 
}

void Executor::visitExtractValue(ExtractValueInst &I) {
    // we do not support virtual register with aggregate type
    // because we observe that such operations are usually not related
    auto *V = ES->boundValue(I.getOperand(0));
    assert(V->poison());
    ES->registerAllocate(&I);
    // auto x = ES->boundValue(&I);
    // if(x && !x->poison())
    //     llvm::slice_Inst.insert(&I); 
}

void Executor::visitInsertValue(InsertValueInst &I) {
    // we do not support virtual register with aggregate type
    // because we observe that such operations are usually not related
    ES->registerAllocate(&I);
    // auto x = ES->boundValue(&I);
    // if(x && !x->poison())
    //     llvm::slice_Inst.insert(&I); 
}

void Executor::visitFence(FenceInst &I) {
    errs() << I << "\n";
    llvm_unreachable("Error: lower-atomic fails!");
}

void Executor::visitAtomicCmpXchg(AtomicCmpXchgInst &I) {
    errs() << I << "\n";
    llvm_unreachable("Error: lower-atomic fails!");
}

void Executor::visitAtomicRMW(AtomicRMWInst &I) {
    errs() << I << "\n";
    llvm_unreachable("Error: lower-atomic fails!");
}

void Executor::visitTrunc(TruncInst &I) {
    trunc(&I, I.getOperand(0));
    // auto x = ES->boundValue(&I);
    // if(x && !x->poison())
    //     llvm::slice_Inst.insert(&I); 
}

void Executor::visitZExt(ZExtInst &I) {
    zext(&I, I.getOperand(0));
    // auto x = ES->boundValue(&I);
    // if(x && !x->poison())
    //     llvm::slice_Inst.insert(&I); 
}

void Executor::visitSExt(SExtInst &I) {
    sext(&I, I.getOperand(0));
    // auto x = ES->boundValue(&I);
    // if(x && !x->poison())
    //     llvm::slice_Inst.insert(&I); 
}

void Executor::visitFPToUI(FPToUIInst &I) {
    auto *DstTy = I.getDestTy();
    auto *SrcTy = I.getSrcTy();

    unsigned DstSz = DL::getNumBytes(DstTy);
    unsigned SrcSz = DL::getNumBytes(SrcTy);
    if (DstSz == SrcSz) {
        ES->bindValue(&I, I.getOperand(0));
    } else if (DstSz < SrcSz) {
        trunc(&I, I.getOperand(0));
    } else {
        zext(&I, I.getOperand(0));
    }
    // auto x = ES->boundValue(&I);
    // if(x && !x->poison())
    //     llvm::slice_Inst.insert(&I);
}

void Executor::visitFPToSI(FPToSIInst &I) {
    auto *DstTy = I.getDestTy();
    auto *SrcTy = I.getSrcTy();

    unsigned DstSz = DL::getNumBytes(DstTy);
    unsigned SrcSz = DL::getNumBytes(SrcTy);
    if (DstSz == SrcSz) {
        ES->bindValue(&I, I.getOperand(0));
    } else if (DstSz < SrcSz) {
        trunc(&I, I.getOperand(0));
    } else {
        sext(&I, I.getOperand(0));
    }
    // auto x = ES->boundValue(&I);
    // if(x && !x->poison())
    //     llvm::slice_Inst.insert(&I);
}

void Executor::visitUIToFP(UIToFPInst &I) {
    auto *DstTy = I.getDestTy();
    auto *SrcTy = I.getSrcTy();

    unsigned DstSz = DL::getNumBytes(DstTy);
    unsigned SrcSz = DL::getNumBytes(SrcTy);
    if (DstSz == SrcSz) {
        ES->bindValue(&I, I.getOperand(0));
    } else if (DstSz < SrcSz) {
        trunc(&I, I.getOperand(0));
    } else {
        zext(&I, I.getOperand(0));
    }
    // auto x = ES->boundValue(&I);
    // if(x && !x->poison())
    //     llvm::slice_Inst.insert(&I);
}

void Executor::visitSIToFP(SIToFPInst &I) {
    auto *DstTy = I.getDestTy();
    auto *SrcTy = I.getSrcTy();

    unsigned DstSz = DL::getNumBytes(DstTy);
    unsigned SrcSz = DL::getNumBytes(SrcTy);
    if (DstSz == SrcSz) {
        ES->bindValue(&I, I.getOperand(0));
    } else if (DstSz < SrcSz) {
        trunc(&I, I.getOperand(0));
    } else {
        sext(&I, I.getOperand(0));
    }
    // auto x = ES->boundValue(&I);
    // if(x && !x->poison())
    //     llvm::slice_Inst.insert(&I);
}

void Executor::visitFPTrunc(FPTruncInst &I) {
    trunc(&I, I.getOperand(0));
    // auto x = ES->boundValue(&I);
    // if(x && !x->poison())
    //     llvm::slice_Inst.insert(&I);
}

void Executor::visitFPExt(FPExtInst &I) {
    sext(&I, I.getOperand(0));
    // auto x = ES->boundValue(&I);
    // if(x && !x->poison())
    //     llvm::slice_Inst.insert(&I);
}

void Executor::visitPtrToInt(PtrToIntInst &I) {
    ES->registerAllocate(&I);
    // auto x = ES->boundValue(&I);
    // if(x && !x->poison())
    //     llvm::slice_Inst.insert(&I);
}

void Executor::visitIntToPtr(IntToPtrInst &I) {
    ES->registerAllocate(&I);
    // auto x = ES->boundValue(&I);
    // if(x && !x->poison())
    //     llvm::slice_Inst.insert(&I);
}

void Executor::visitBitCast(BitCastInst &I) {
    inferDITypeBitCast(I);
    ES->bindValue(&I, I.getOperand(0));
    // auto x = ES->boundValue(&I);
    // if(x && !x->poison())
    //     llvm::slice_Inst.insert(&I);
}

void Executor::visitAddrSpaceCast(AddrSpaceCastInst &I) {
    ES->bindValue(&I, I.getOperand(0));
    // if(x && !x->poison())
    //     llvm::slice_Inst.insert(&I);
}

void Executor::visitFreeze(FreezeInst &I) {
    ES->bindValue(&I, I.getOperand(0));
    // if(x && !x->poison())
    //     llvm::slice_Inst.insert(&I);
}

void Executor::visitCleanupPad(CleanupPadInst &I) {
    errs() << I << "\n";
    llvm_unreachable("Error: lower-invoke fails or not C code!");
}

void Executor::visitCatchPad(CatchPadInst &I) {
    errs() << I << "\n";
    llvm_unreachable("Error: lower-invoke fails or not C code!");
}

void Executor::visitUserOp1(Instruction &I) {
    // do nothing
}

void Executor::visitUserOp2(Instruction &I) {
    // do nothing
}

void Executor::visitExtractElement(ExtractElementInst &I) {
    errs() << I << "\n";
    llvm_unreachable("Error: please use -fno-vectorize to generate bitcode!");
}

void Executor::visitInsertElement(InsertElementInst &I) {
    errs() << I << "\n";
    llvm_unreachable("Error: please use -fno-vectorize to generate bitcode!");
}

void Executor::visitShuffleVector(ShuffleVectorInst &I) {
    errs() << I << "\n";
    llvm_unreachable("Error: please use -fno-vectorize to generate bitcode!");
}

void Executor::visitLandingPad(LandingPadInst &I) {
    errs() << I << "\n";
    llvm_unreachable("Error: lower-invoke fails or not C code!");
}

void Executor::trunc(Value *DstVal, Value *SrcVal) {
    auto *P = ES->boundValue(SrcVal);
    assert(P);
    auto *ResultVal = ES->registerAllocate(DstVal);
    abs_value::trunc(ResultVal, P);
}

void Executor::zext(Value *DstVal, Value *SrcVal) {
    auto *P = ES->boundValue(SrcVal);
    assert(P);
    auto *ResultVal = ES->registerAllocate(DstVal);
    abs_value::zext(ResultVal, P);
}

void Executor::sext(Value *DstVal, Value *SrcVal) {
    auto *P = ES->boundValue(SrcVal);
    assert(P);
    auto *ResultVal = ES->registerAllocate(DstVal);
    abs_value::sext(ResultVal, P);
}

void Executor::visitSSQBufStrLen(CallInst &I) {
    auto *Len = ES->registerAllocate(&I);
    Len->set(Z3::bv_const("strlen", Len->bytewidth() * 8) - 1);
    // if(!Len->poison()) 
    //     llvm::slice_Inst.insert(&I); 
}

GlobalMemoryBlock *Executor::isConstantString(Value *PtrVal) {
    auto *PtrAbsVal = dyn_cast_or_null<AddressValue>(ES->boundValue(PtrVal));
    if (!PtrAbsVal || PtrAbsVal->poison() || PtrAbsVal->size() != 1) return nullptr;
    auto *GM = dyn_cast_or_null<GlobalMemoryBlock>(PtrAbsVal->base(0));
    // constant string should be defined as a global var in llvm bitcode
    if (!GM) return nullptr;
    // we never find a case with a positive offset for constant string
    auto OffsetExpr = PtrAbsVal->offset(0);
    uint64_t Offset;
    if (!Z3::is_numeral_u64(OffsetExpr, Offset) || Offset != 0) return nullptr;
    // string in llvm bitcode is a constant data array
    if (!GM->isConstantDataArray()) return nullptr;
    auto *FirstByte = GM->at(Offset);
    if (!isa_and_nonnull<ScalarValue>(FirstByte)) return nullptr;
    // the constant data array must be a byte array
    if (FirstByte->bytewidth() != 1) return nullptr;
    assert(!FirstByte->poison());
    return GM;
}

void Executor::recordMemoryWritten(Instruction *I, MemoryBlock *Mem, AbstractValue *Key) {
    if (!LoopStack.empty()) LoopStack.back()->recordMemoryRevised(Key);
    if (auto *StackMem = dyn_cast<StackMemoryBlock>(Mem))
        if (!I || StackMem->getFunction() == I->getFunction()) return;
    EscapedMemoryRevision.insert(Key);
}

void Executor::recordMemoryRead(Instruction *I, MemoryBlock *Mem, AbstractValue *LoadedAbsValue) {
    if (!LoopStack.empty() && isa<MessageBuffer>(Mem)) {
        if (!LoadedAbsValue->poison() && isa<ScalarValue>(LoadedAbsValue)) {
            auto ByteSeq = LoadedAbsValue->value();
            if (ByteSeq.decl().decl_kind() == Z3_OP_SELECT) {
                assert(ByteSeq.get_sort().bv_size() == 8);
                LoopStack.back()->recordBytesLoaded(ByteSeq);
            } else if (ByteSeq.decl().decl_kind() == Z3_OP_CONCAT) {
                for (unsigned K = 0; K < ByteSeq.num_args(); ++K) {
                    auto Byte = ByteSeq.arg(K);
                    assert(Byte.get_sort().bv_size() == 8);
                    assert(Byte.decl().decl_kind() == Z3_OP_SELECT);
                    LoopStack.back()->recordBytesLoaded(Byte);
                }
            } else if (ByteSeq.decl().decl_kind() == Z3_OP_BNUM) {

            } else {
                llvm_unreachable("Error: unknown seq loaded from message buffer");
            }
        }
    }
}

void Executor::visitStrNCmp(CallInst &I) {
    visitCallDefault(I);
    if (I.getNumArgOperands() != 3 || !I.getType()->isIntegerTy()) return;

    auto N = I.getArgOperand(2);
    auto NVal = ES->boundValue(N);
    if (!isa_and_nonnull<ScalarValue>(NVal) || NVal->poison()) return;

    uint64_t Len;
    if (!NVal->uint64(Len) || Len == 0 || Len > 20) return;

    auto *Op1 = I.getArgOperand(0); // the const str
    auto *Op2 = I.getArgOperand(1); // the buffer

    GlobalMemoryBlock *ConstString = nullptr;
    if (auto *Ret1 = isConstantString(Op1)) {
        ConstString = Ret1;
    } else if (auto *Ret2 = isConstantString(Op2)) {
        ConstString = Ret2;
        auto *Tmp = Op1;
        Op1 = Op2;
        Op2 = Tmp;
    } else {
        return;
    }
    if (ConstString->size() < Len) return;

    auto *Op2AbsVal = dyn_cast_or_null<AddressValue>(ES->boundValue(Op2));
    if (!Op2AbsVal || Op2AbsVal->poison() || Op2AbsVal->size() != 1) return;
    auto *M = dyn_cast_or_null<MessageBuffer>(Op2AbsVal->base(0));
    if (!M) return;
    auto Off = Op2AbsVal->offset(0);
    auto ResExpr = M->at(Off)->value() == ConstString->at(0)->value();
    for (unsigned K = 1; K < Len; ++K) {
        auto NewOff = Z3::add(Off, Z3::bv_val(K, Off.get_sort().bv_size()));
        ResExpr = ResExpr && M->at(NewOff)->value() == ConstString->at(K)->value();
    }
    auto *ResAbsVal = dyn_cast_or_null<ScalarValue>(ES->boundValue(&I));
    ResAbsVal->set(Z3::bool_to_bv(Z3::negation(ResExpr), ResAbsVal->bytewidth() * 8));
    // if(!ResAbsVal->poison()) 
    //     llvm::slice_Inst.insert(&I); 
}

void Executor::visitStrCmp(CallInst &I) {
    visitCallDefault(I);
    if (I.getNumArgOperands() != 2 || !I.getType()->isIntegerTy()) return;

    auto *Op1 = I.getArgOperand(0); // the const str
    auto *Op2 = I.getArgOperand(1); // the buffer

    GlobalMemoryBlock *ConstString = nullptr;
    if (auto *Ret1 = isConstantString(Op1)) {
        ConstString = Ret1;
    } else if (auto *Ret2 = isConstantString(Op2)) {
        ConstString = Ret2;
        auto *Tmp = Op1;
        Op1 = Op2;
        Op2 = Tmp;
    } else {
        return;
    }
    unsigned Len = ConstString->size();
    if (Len > 20) return;

    auto *Op2AbsVal = dyn_cast_or_null<AddressValue>(ES->boundValue(Op2));
    if (!Op2AbsVal) return;
    if (Op2AbsVal->poison() || Op2AbsVal->size() != 1) return;
    auto *M = dyn_cast_or_null<MessageBuffer>(Op2AbsVal->base(0));
    if (!M) return;
    auto Off = Op2AbsVal->offset(0);
    auto ResExpr = M->at(Off)->value() == ConstString->at(0)->value();
    for (unsigned K = 1; K < Len; ++K) {
        auto NewOff = Z3::add(Off, Z3::bv_val(K, Off.get_sort().bv_size()));
        ResExpr = ResExpr && M->at(NewOff)->value() == ConstString->at(K)->value();
    }
    auto *ResAbsVal = dyn_cast_or_null<ScalarValue>(ES->boundValue(&I));
    ResAbsVal->set(Z3::bool_to_bv(Z3::negation(ResExpr), ResAbsVal->bytewidth() * 8));
    // if(!ResAbsVal->poison()) 
    //     llvm::slice_Inst.insert(&I); 
}

void Executor::visitpardiffMakeMessage(CallInst &I) {
    // we create a scalable vector with initial size 200
    alloc(MemoryBlock::MK_Message, &I, IntegerType::get(I.getContext(), 8), 200);
}

void Executor::visitpardiffMakeMessageLen(CallInst &I) {
    auto *Len = ES->registerAllocate(&I);
    Len->set(Z3::length(Len->bytewidth() * 8));
}

void Executor::visitpardiffMakeNamedObject(CallInst &I) {
    assert(I.arg_size() == 2);
    assert(I.getType()->isPointerTy());
    auto *ByteVal = dyn_cast<ConstantInt>(I.getArgOperand(0));
    assert(ByteVal);
    uint64_t Bitwidth = ByteVal->getZExtValue() * 8;
    auto *NameGV = dyn_cast<GlobalVariable>(I.getArgOperand(1)->stripInBoundsConstantOffsets());
    assert(NameGV && NameGV->isConstant());
    auto *CDA = dyn_cast<ConstantDataArray>(NameGV->getInitializer());
    assert(CDA && CDA->isCString());
    auto Name = CDA->getAsCString();

    auto *NamedObjPtr = ES->registerAllocate(&I);
    auto Addr = ES->globalAllocate(Type::getIntNTy(I.getContext(), Bitwidth));
    ((AddressValue *) NamedObjPtr)->assign(Addr);
    auto *NamedObj = Addr->at(0);
    NamedObj->set(Z3::bv_const(Name.str().c_str(), Bitwidth));
}

void Executor::visitMemCpy(CallInst &I) {
    auto *Dst = I.getArgOperand(0);
    auto *DstAV = cast<AddressValue>(ES->boundValue(Dst));
    auto *Src = I.getArgOperand(1);
    auto *SrcAV = cast<AddressValue>(ES->boundValue(Src));
    auto *Len = I.getArgOperand(2);
    auto *LenAV = ES->boundValue(Len);
    // if(!DstAV->poison() && !SrcAV->poison() && !LenAV->poison())
    //     llvm::slice_Inst.insert(&I); 
    if (!I.getType()->isVoidTy()) {
        // memcpy may return the dst ptr
        assert(I.getType()->isPointerTy());
        ES->registerAllocate(&I)->assign(DstAV);
    }

    if (isa<ConstantInt>(Len)) {
        int64_t LenInt = ((ConstantInt *) Len)->getSExtValue();
        assert(LenInt >= 0);
        memoryCopy(&I, DstAV, SrcAV, LenInt);

        if (EnableNaming && SrcAV->size() == 1 && isa_and_nonnull<MessageBuffer>(SrcAV->base(0))) {
            auto Name = getStructFieldName(Dst);
            if (Name != UNKNOWN_NAME) {
                auto *Mem = (MessageBuffer *) SrcAV->base(0);
                auto StartIndex = SrcAV->offset(0);
                ES->addPC(Z3::naming(Mem->at(StartIndex, LenInt), Name.c_str()));
            }
        }
    } else {
        assert(LenAV);
        memoryCopy(&I, DstAV, SrcAV, LenAV);
    }
}

void Executor::visitMemMov(CallInst &I) {
    // The ‘llvm.memmove.*’ intrinsics move a block of memory from the source location to the destination location.
    // It is similar to the ‘llvm.memcpy’ intrinsic but allows the two memory locations to overlap.
    visitMemCpy(I);
}

void Executor::visitMemSet(CallInst &I) {
    // memset is often used to zero-initialize a memory block, which we often do not care about
    visitCallDefault(I);

    auto *Dst = I.getArgOperand(0);
    auto *Val = I.getArgOperand(1);
    auto *Len = I.getArgOperand(2);

    auto *DstAbsVal = ES->boundValue(Dst);
    if (DstAbsVal->poison()) return;
    auto Addr = dyn_cast<AddressValue>(DstAbsVal);
    assert(Addr);
    if (Addr->size() != 1) return;
    auto *Mem = Addr->base(0);
    auto OffsetExpr = Addr->offset(0);
    uint64_t Offset;
    if (!Z3::is_numeral_u64(OffsetExpr, Offset)) return;

    auto *ValAbsVal = ES->boundValue(Val);
    uint64_t Const;
    if (ValAbsVal->uint64(Const) && Const == 0) {
        // it is to zero-initialize something
        auto *LenAbsVal = ES->boundValue(Len);
        if (LenAbsVal->uint64(Const)) {
            unsigned LenSet = 0;
            while (LenSet < Const) {
                auto DstKey = Mem->at(Offset + LenSet);
                auto *DstVal = ES->getValue(DstKey, true);
                if (!DstVal) {
                     pardiff_WARN("memset constant length but the memory length is not constant.");
                     break;
                 }
                DstVal->zeroInitialize();
                LenSet += DstVal->bytewidth();
                recordMemoryWritten(&I, Mem, DstKey);
            }
        }
    }
    // if(!ValAbsVal->poison()) 
    //     llvm::slice_Inst.insert(&I); 
}

void Executor::visitMemCmp(CallInst &I) {
    visitCallDefault(I);
    if (I.getNumArgOperands() != 3 || !I.getType()->isIntegerTy()) return;

    auto N = I.getArgOperand(2);
    auto NVal = ES->boundValue(N);
    if (!isa_and_nonnull<ScalarValue>(NVal) || NVal->poison()) return;

    uint64_t NumBytes2Cmp;
    if (!NVal->uint64(NumBytes2Cmp) || NumBytes2Cmp == 0 || NumBytes2Cmp > 20) return;

    auto *Op1 = I.getArgOperand(0);
    auto *Op1AbsVal = dyn_cast_or_null<AddressValue>(ES->boundValue(Op1));
    if (!Op1AbsVal || Op1AbsVal->poison() || Op1AbsVal->size() != 1) return;
    auto *M1 = Op1AbsVal->base(0);
    auto Off1 = Op1AbsVal->offset(0);
    uint64_t O1;
    if (!isa<MessageBuffer>(M1) && !Z3::is_numeral_u64(Off1, O1)) return;
    z3::expr_vector Vec1 = Z3::vec();
    for (unsigned K = 0; K < NumBytes2Cmp;) {
        auto A1 = M1->at(Z3::add(Off1, Z3::bv_val(K, Off1.get_sort().bv_size())));
        if (!A1 || A1->poison()) return;
        if (K + A1->bytewidth() <= NumBytes2Cmp) {
            // we use byteswap as we assume little-endian
            Vec1.push_back(A1->bytewidth() == 1 ? A1->value() : Z3::byteswap(A1->value()));
        } else {
            assert(A1->bytewidth() > 1);
            auto Bytes2Extract = K + A1->bytewidth() - NumBytes2Cmp;
            auto H = A1->bytewidth() * 8 - 1;
            auto L = (A1->bytewidth() - Bytes2Extract) * 8;
            Vec1.push_back(Z3::extract(Z3::byteswap(A1->value()), H, L));
        }
        K += A1->bytewidth();
    }
    auto V1 = Z3::concat(Vec1);

    auto *Op2 = I.getArgOperand(1);
    auto *Op2AbsVal = dyn_cast_or_null<AddressValue>(ES->boundValue(Op2));
    if (!Op2AbsVal || Op2AbsVal->poison() || Op2AbsVal->size() != 1) return;
    auto *M2 = Op2AbsVal->base(0);
    auto Off2 = Op2AbsVal->offset(0);
    uint64_t O2;
    if (!isa<MessageBuffer>(M2) && !Z3::is_numeral_u64(Off2, O2)) return;
    z3::expr_vector Vec2 = Z3::vec();
    for (unsigned K = 0; K < NumBytes2Cmp;) {
        auto A2 = M2->at(Z3::add(Off2, Z3::bv_val(K, Off2.get_sort().bv_size())));
        if (!A2 || A2->poison()) return;
        if (K + A2->bytewidth() <= NumBytes2Cmp) {
            // we use byteswap as we assume little-endian
            Vec2.push_back(A2->bytewidth() == 1 ? A2->value() : Z3::byteswap(A2->value()));
        } else {
            assert(A2->bytewidth() > 1);
            auto Bytes2Extract = K + A2->bytewidth() - NumBytes2Cmp;
            auto H = A2->bytewidth() * 8 - 1;
            auto L = (A2->bytewidth() - Bytes2Extract) * 8;
            Vec1.push_back(Z3::extract(Z3::byteswap(A2->value()), H, L));
        }
        K += A2->bytewidth();
    }
    auto V2 = Z3::concat(Vec2);

    // we use Z3::ne because the return value 0 of memcmp means true.
    auto *ResAbsVal = dyn_cast_or_null<ScalarValue>(ES->boundValue(&I));
    ResAbsVal->set(Z3::bool_to_bv(Z3::ne(V1, V2), ResAbsVal->bytewidth() * 8));
    // if(!ResAbsVal->poison()) 
    //     llvm::slice_Inst.insert(&I); 
}

void Executor::visitByteSwap(CallInst &I) {
    assert(!I.getType()->isVoidTy());
    assert(I.arg_size() == 1);
    auto *Result = ES->registerAllocate(&I);
    auto *AbsVal = ES->boundValue(I.getArgOperand(0));
    assert(isa_and_nonnull<ScalarValue>(AbsVal));
    assert(isa_and_nonnull<ScalarValue>(Result));
    if (AbsVal->poison()) return;
    Result->set(Z3::byteswap(AbsVal->value()));
    // if(!Result->poison()) 
    //     llvm::slice_Inst.insert(&I); 
}

void Executor::visitIsConstant(CallInst &I) {
    // This intrinsic generates no code. If its argument is known to be a manifest compile-time constant value,
    // then the intrinsic will be converted to a constant true value. Otherwise, it will be converted to a constant
    // false value.
    //
    // no matter it returns true or false, the semantics are preserved.
    auto AbsVal = ES->registerAllocate(&I);
    AbsVal->set(Z3::bv_val(1, AbsVal->bytewidth() * 8));
    // if(!AbsVal->poison()) 
    //     llvm::slice_Inst.insert(&I); 
}

void Executor::visitMalloc(CallInst &I) {
    if (I.getNumArgOperands() != 1) {
        // not a malloc...
        visitCallDefault(I);
        return;
    }

    // we use i8 as the default allocated type
    Type *AllocatedTy = IntegerType::get(I.getContext(), 8);
    auto *Next = I.getNextNode();
    if (auto *Cast = dyn_cast<BitCastInst>(Next)) {
        if (Cast->getOperand(0) == &I) {
            // guess the malloc type.
            auto *AllocatedTyPtrTy = Cast->getDestTy();
            if (AllocatedTyPtrTy->isPointerTy())
                AllocatedTy = AllocatedTyPtrTy->getPointerElementType();
        }
    }
    int64_t NumBytes = 1;
    auto *NumByteValue = I.getArgOperand(0);
    auto *NumByteAbsVal = ES->boundValue(NumByteValue);
    if (!NumByteAbsVal->poison()) {
        // llvm::slice_Inst.insert(&I); 
        if (!Z3::is_numeral_i64(NumByteAbsVal->value(), NumBytes) || NumBytes <= 0) {
            NumBytes = 1;
        }
    }
    unsigned AllocatedTySz = DL::getNumBytes(AllocatedTy);
    unsigned AllocatedNum = 1;
    if (NumBytes >= AllocatedTySz && NumBytes % AllocatedTySz == 0) {
        AllocatedNum = NumBytes / AllocatedTySz;
    }

    alloc(MemoryBlock::MK_Heap, &I, AllocatedTy, AllocatedNum == 0 ? 1 : AllocatedNum);
}

void Executor::visitCalloc(CallInst &I) {
    if (I.getNumArgOperands() != 2) {
        // not a calloc...
        visitCallDefault(I);
        return;
    }

    // we use i8 as the default allocated type
    Type *AllocatedTy = IntegerType::get(I.getContext(), 8);
    auto *Next = I.getNextNode();
    if (auto *Cast = dyn_cast<BitCastInst>(Next)) {
        if (Cast->getOperand(0) == &I) {
            // guess the malloc type.
            auto *AllocatedTyPtrTy = Cast->getDestTy();
            if (AllocatedTyPtrTy->isPointerTy())
                AllocatedTy = AllocatedTyPtrTy->getPointerElementType();
        }
    }
    int64_t TypeSize = 1;
    auto *TypeSzValue = I.getArgOperand(1);
    auto *TySzAbsVal = ES->boundValue(TypeSzValue);
    if (!TySzAbsVal->poison()) {
        // llvm::slice_Inst.insert(&I); 
        if (!Z3::is_numeral_i64(TySzAbsVal->value(), TypeSize) || TypeSize <= 0) {
            TypeSize = 1;
        }
    }
    unsigned AllocatedTySz = DL::getNumBytes(AllocatedTy);
    unsigned AllocatedNum = 1;
    if (TypeSize >= AllocatedTySz && TypeSize % AllocatedTySz == 0) {
        AllocatedNum = TypeSize / AllocatedTySz;
    }

    int64_t Count;
    auto *CountValue = I.getArgOperand(0);
    auto *CountAbsVal = ES->boundValue(CountValue);
    if (!CountAbsVal->poison()) {
        // llvm::slice_Inst.insert(&I); 
        if (Z3::is_numeral_i64(CountAbsVal->value(), Count) && Count > 0) {
            AllocatedNum *= Count;
        }
    }

    alloc(MemoryBlock::MK_Heap, &I, AllocatedTy, AllocatedNum == 0 ? 1 : AllocatedNum);
}

void Executor::visitDbgValue(DbgValueInst &I) {
    if (!EnableNaming) return;
    if (I.getExpression()->getNumElements()) return; // we do not handle complex dbg expressions
    auto *Val = I.getValue();
    auto *DIVar = I.getVariable();
    naming(I.getFunction(), Val, DIVar);

    if (auto *DITy = DIVar->getType()) {
        ValueDebugTypeMap[Val] = DITy;
    }
}

void Executor::visitDbgDeclare(DbgDeclareInst &I) {
    if (!EnableNaming) return;
    if (I.getExpression()->getNumElements()) return; // we do not handle complex dbg expressions
    auto *Val = I.getVariableLocation();
    if (!isa<Constant>(Val->stripPointerCasts()) && !isa<AllocaInst>(Val->stripPointerCasts())) return;
    auto *DIVar = I.getVariable();
    naming(I.getFunction(), Val, DIVar);

    if (auto *DITy = DIVar->getType()) {
        auto *PtrTy = DL::getDIPointerType(DITy);
        ValueDebugTypeMap[Val] = PtrTy;
    }
}

void Executor::visitCallDefault(CallInst &I) {
    // llvm::slice_Inst.insert(&I); 
    if (!I.getType()->isVoidTy()) ES->registerAllocate(&I);
}

struct CallFrame {
    AbstractValue *RetValReceiver; // the receiver at the call site
    Executor *Exe; // old state pointer, should reset after returning from the callee
    CallInst *CallSite; // the call site
    unsigned PCSize; // the current length of pc at the call site
};
static std::vector<CallFrame> CallStack;
static std::set<Function *> CalleeSet;

void Executor::visitCallIPA(CallInst &I) {
    // if(CallStack.size>2){
    //     visitCallDefault(I);
    //     return;
    // }
    DEBUG_WITH_TYPE("L2CAP",
                    if (DebugL2CAPChannel.getNumOccurrences() && CallStack.size() == 2) {
                        auto FN = I.getCalledFunction()->getName();
                        if (FN.endswith("_channel") && FN != DebugL2CAPChannel) {
                            visitCallDefault(I);
                            return;
                        }
                    }
    );

    DEBUG_WITH_TYPE("SSQ",
                    if (DebugSSQChannel.getNumOccurrences() && CallStack.size() == 1) {
                        auto FN = I.getCalledFunction()->getName();
                        if (FN.endswith("_deserialize") && FN != DebugSSQChannel) {
                            visitCallDefault(I);
                            return;
                        }
                    }
    );

    auto *Callee = I.getCalledFunction();
    assert(Callee);
    if (CalleeSet.count(Callee)) {
        if (!EnableRecursiveCall) {
            visitCallDefault(I);
            return;
        } else {
            errs() << "[Call Stack]\n";
            errs() << Callee->getName() << " <<< \n";
            while (!CallStack.empty()) {
                auto CS = CallStack.back().CallSite;
                if (!CS) break;
                auto PrevCalleeName = CS->getCalledFunction()->getName();
                errs() << PrevCalleeName;
                if (PrevCalleeName == Callee->getName()) {
                    errs() << " <<< \n";
                } else {
                    errs() << "\n";
                }
                CallStack.pop_back();
            }
            llvm_unreachable("TODO : function is recursively called!");
        }
    }
    CalleeSet.insert(Callee);
    if (I.getType()->isVoidTy()) {
        CallStack.push_back({nullptr, this, &I, ES->pcLength()});
    } else {
        CallStack.push_back({ES->registerAllocate(&I), this, &I, ES->pcLength()});
    }

    Executor CalleeExectuor(DriverPass);
    CalleeExectuor.StateMap[&Callee->getEntryBlock()].push_back(ES);
    // prepare parameters
    for (unsigned K = 0; K < Callee->arg_size(); ++K) {
        auto *FormalArg = Callee->getArg(K);
        auto *ActualArg = I.getArgOperand(K);
        auto *FormalArgAV = ES->registerAllocate(FormalArg);
        auto *ActualArgAV = ES->boundValue(ActualArg);
        FormalArgAV->assign(ActualArgAV);
    }
    ES->markCall();
    //llvm::slice_Inst.insert(&I); 
    CalleeExectuor.visit(Callee);
}

void Executor::visitRet(ReturnInst &I) {
    auto *Caller = I.getFunction();
    pardiff_INFO(">Returning " << space(CallStack.size() - 1) << Caller->getName() << "@" << getCounter(Caller));
    if (CallStack.size() > 1) {
        packing(I); // if the called function is too complex, just pack them to a predicate
        auto *Receiver = CallStack.back().RetValReceiver;
        if (Receiver) {
            assert(I.getNumOperands());
            auto *RetVal = I.getOperand(0);
            auto *RetValAbsVal = ES->boundValue(RetVal);
            Receiver->assign(RetValAbsVal);
        }
        auto *CallerExecutor = CallStack.back().Exe;
        CallerExecutor->ES = ES;
        CallerExecutor->EscapedMemoryRevision.insert(EscapedMemoryRevision.begin(), EscapedMemoryRevision.end());
        if (!CallerExecutor->LoopStack.empty())
            for (auto *Abs: EscapedMemoryRevision)
                CallerExecutor->LoopStack.back()->recordMemoryRevised(Abs);
        CallStack.pop_back();
        CalleeSet.erase(I.getParent()->getParent()); // to test recursive call

        // gc stack and register
        ES->gc(I.getParent()->getParent());
    } else {
        std::vector<CallFrame>().swap(CallStack);
        std::set<Function *>().swap(CalleeSet);
        ES->gc(I.getParent()->getParent());
        PC = ES->pc();
    }
    //llvm::slice_Inst.insert(&I); 
}

void Executor::alloc(MemoryBlock::MemoryKind MemTy, Instruction *Ret, Type *AllocTy, unsigned Num) {
    // allocate space for the target type
    MemoryBlock *Addr = nullptr;
    switch (MemTy) {
        case MemoryBlock::MK_Stack:
            Addr = ES->stackAllocate(Ret->getFunction(), AllocTy, Num);
            break;
        case MemoryBlock::MK_Heap:
            Addr = ES->heapAllocate(AllocTy, Num);
            break;
        case MemoryBlock::MK_Message:
            Addr = ES->messageAllocate(AllocTy, Num);
            break;
        default:
            llvm_unreachable("Error : unknown memory type!");
    }

    // allocate space for the pointer
    auto *PointerVal = ES->registerAllocate(Ret);
    // let the returning pointer points-to the space
    cast<AddressValue>(PointerVal)->assign(Addr);
}

void Executor::beforeVisit(Instruction &I) {
    Inst.insert(&I);
    if (auto *CI = dyn_cast<CallInst>(&I)) {
        switch (CI->getIntrinsicID()) {
            case Intrinsic::dbg_addr:
            case Intrinsic::dbg_label:
            case Intrinsic::lifetime_start:
            case Intrinsic::lifetime_end:
                return;
        }
    }
    DEBUG_FUNC(I.getFunction(), {
        dbgs() << "************************************\n";
        dbgs() << "[Before Visiting] " << I << " ...\n";
        if (I.hasMetadata("dbg")) {
            dbgs() << "[Source File] " << I.getDebugLoc().get()->getFilename() << "\n";
            dbgs() << "[Source Line] " << I.getDebugLoc().get()->getLine() << "\n";
        }
        dbgs() << "[Func] " << I.getParent()->getParent()->getName() << "\n";
        dbgs() << "[Loop] " << (LoopStack.empty() ? "null" : std::to_string(LoopStack.back()->getTripCount())) << "\n";
        dbgs() << "************************************\n";
    });
    if (DebugSrcLine.getNumOccurrences() && I.hasMetadata("dbg") && I.getDebugLoc().getLine() == DebugSrcLine) {
        outs() << "";
    }
}

void Executor::afterVisit(Instruction &I) {
    bool DebugIntrinsic = false;
    if (auto *CI = dyn_cast<CallInst>(&I)) {
        switch (CI->getIntrinsicID()) {
            case Intrinsic::dbg_value:
            case Intrinsic::dbg_declare:
                DebugIntrinsic = true;
                break;
            case Intrinsic::dbg_addr:
            case Intrinsic::dbg_label:
            case Intrinsic::lifetime_start:
            case Intrinsic::lifetime_end:
                return;
        }
    }
    DEBUG_FUNC(I.getFunction(), {
        dbgs() << "************************************\n";
        dbgs() << "[After Visiting] " << I << " ... \n";
        
        if (!I.getType()->isVoidTy()){
            auto x =  ES->boundValue(&I);
            if(x){
                if(!(x->poison()))
                    slice_Inst.insert(&I);
            }
            dbgs() << "[Abstract Value] " << x->str() << "\n";
        } 
        
        for (unsigned K = 0; !DebugIntrinsic && K < I.getNumOperands(); ++K) {
            if (auto BoundVal = ES->boundValue(I.getOperand(K)))
                dbgs() << "[" << K << "] " << BoundVal->str() << "\n";
            else
                dbgs() << "[" << K << "] gc'ed\n";
        }
        if (I.hasMetadata("dbg")) {
            dbgs() << "[Source File] " << I.getDebugLoc().get()->getFilename() << "\n";
            dbgs() << "[Source Line] " << I.getDebugLoc().get()->getLine() << "\n";
        }
        auto It = ValueDebugTypeMap.find(&I);
        if (It != ValueDebugTypeMap.end()) {
            dbgs() << "[Source Type] " << It->second->getName() << "\n";
        }
        dbgs() << "====================================\n";
        dbgs() << *ES << "\n";
        dbgs() << "************************************\n";
    });
    if (DebugSrcLine.getNumOccurrences() && I.hasMetadata("dbg") && I.getDebugLoc().getLine() == DebugSrcLine) {
        outs() << "";
    }
    if (isa<ReturnInst>(I)) { // we can set breakpoint at this line...
        dbgs() << ""; // sometimes when debugging, we need to skip to ret, set breakpoint here...
    }
}

static void search(BasicBlock *B,
                   std::set<BasicBlock *> &VisitedBlocks,
                   std::list<BasicBlock *> &DFSList,
                   std::vector<std::list<BasicBlock *>::iterator> &WorkList,
                   FunctionLoopInformation *FLI) {
    VisitedBlocks.insert(B);

    if (auto *LP = FLI->isLoopHeader(B)) {
        for (auto It = LP->exit_begin(), E = LP->exit_end(); It != E; ++It) {
            auto *Succ = *It;
            if (!VisitedBlocks.count(Succ)) {
                search(Succ, VisitedBlocks, DFSList, WorkList, FLI);
            }
        }
        DFSList.push_front(B);
        WorkList.push_back(DFSList.begin());
    } else {
        for (auto It = succ_begin(B), E = succ_end(B); It != E; ++It) {
            auto *Succ = *It;
            if (!VisitedBlocks.count(Succ)) {
                search(Succ, VisitedBlocks, DFSList, WorkList, FLI);
            }
        }
        DFSList.push_front(B);
    }
}

static void searchLoop(BasicBlock *B, SingleLoop *Loop,
                       std::set<BasicBlock *> &VisitedBlocks,
                       std::list<BasicBlock *> &DFSList,
                       FunctionLoopInformation *FLI) {
    VisitedBlocks.insert(B);

    auto *LP = FLI->isLoopHeader(B);
    if (LP && LP != Loop) {
        for (auto It = LP->exit_begin(), E = LP->exit_end(); It != E; ++It) {
            auto *Succ = *It;
            if (!VisitedBlocks.count(Succ) && Loop->contains(Succ)) {
                searchLoop(Succ, Loop, VisitedBlocks, DFSList, FLI);
            }
        }
    } else {
        for (auto It = succ_begin(B), E = succ_end(B); It != E; ++It) {
            auto *Succ = *It;
            if (!VisitedBlocks.count(Succ) && Loop->contains(Succ)) {
                searchLoop(Succ, Loop, VisitedBlocks, DFSList, FLI);
            }
        }
    }

    DFSList.push_front(B);
}

void Executor::sortBlocks(Function &F, std::vector<BasicBlock *> &DFSOrderVec) {
    // sort blocks in a depth-first order and keep blocks in a loop consecutive in DFSOrderVec
    auto &Entry = F.getEntryBlock();
    std::vector<std::list<BasicBlock *>::iterator> WorkList;
    std::list<BasicBlock *> OrderedList;
    std::set<BasicBlock *> VisitedBlockSet;
    search(&Entry, VisitedBlockSet, OrderedList, WorkList, FLI);
    while (!WorkList.empty()) {
        auto It = WorkList.back();
        WorkList.pop_back();
        auto *LoopHead = *It;
        It = OrderedList.erase(It);

        VisitedBlockSet.clear();
        std::list<BasicBlock *> LPOrderedList;
        searchLoop(LoopHead, FLI->isLoopHeader(LoopHead), VisitedBlockSet, LPOrderedList, FLI);
        for (auto X: LPOrderedList) {
            auto XIt = OrderedList.insert(It, X);
            if (FLI->isLoopHeader(X) && X != LoopHead) {
                WorkList.push_back(XIt);
            }
        }
    }
    if (F.size() != OrderedList.size()) {
        errs() << "F.size() = " << F.size() << "\n";
        errs() << "OrderedList.size() = " << OrderedList.size() << "\n";
    }
    assert(F.size() == OrderedList.size());
    for (auto *B: OrderedList) DFSOrderVec.push_back(B);
}

void Executor::visitFunction(Function &F) {
    DEBUG_FUNC(&F, dbgs() << "Start to analyze function " + F.getName() + "...\n");

    // entry function, no call inst for the entry function, so we push the call stack here
    if (CallStack.empty()) {
        CallStack.push_back({nullptr, nullptr, nullptr, 0});
        ES = new ExecutionState;
        ES->markCall();

        // set the entry state of the main function
        auto &Entry = F.getEntryBlock();
        auto It = StateMap.find(&Entry);
        assert (It == StateMap.end());
        StateMap[&Entry].push_back(ES);
        initializeGlobals(F);
    }

    // count how many times this function is called, for debugging purposes
    setCounter(&F);
    pardiff_INFO("Processing " << space(CallStack.size() - 1) << F.getName() << "@" << getCounter(&F));

    // collecting the loop information
    FLI = DriverPass->getAnalysis<LoopInformationAnalysis>().getLoopInfo(F);
    DMA = &DriverPass->getAnalysis<DistinctMetadataAnalysis>();

    // sort blocks
    std::vector<BasicBlock *> DFSOrderVec;
    sortBlocks(F, DFSOrderVec);

    // set loop header index
    for (unsigned I = 0; I < DFSOrderVec.size(); ++I) {
        auto *B = DFSOrderVec[I];
        if (auto *LP = FLI->isLoopHeader(B)) {
            LoopHeaderIdxMap[LP] = I;
        }
    }
    unsigned RealBlockNum = DFSOrderVec.size();
    while (RealBlockNum > 0) {
        auto *LastBlock = DFSOrderVec[RealBlockNum - 1];
        if (isa<ReturnInst>(LastBlock->getTerminator())) {
            break;
        } else {
            // pop unreachable blocks that are not necessary to analyze
            // we will do garbage collection after analyzing a return instruction
            // thus, we cannot analyze other unreachable blocks analyzed after the return inst
            RealBlockNum--;
        }
    }
    if (RealBlockNum == 0) {
        errs() << F.getName() << "\n";
        llvm_unreachable("Error: reach a function never returns!");
    }

    // the initial state of a function
    DEBUG_FUNC(&F, {
        auto &Entry = F.getEntryBlock();
        auto It = StateMap.find(&Entry);
        auto XES = It->second[0];
        for (unsigned I = 0; I < F.arg_size(); ++I)
            dbgs() << *F.getArg(I) << " ... " << XES->boundValue(F.getArg(I))->str() << "\n";
    });

    std::vector<BasicBlock *> AnalyzedBlocks; // for debug only
    std::vector<BasicBlock *> SkippedBlocks; // for debug only
    // start data flow analysis
    for (ProcessingBlockPointer = 0; ProcessingBlockPointer < RealBlockNum;) {
        auto *B = DFSOrderVec[ProcessingBlockPointer];
        auto StateIt = StateMap.find(B);
        if (StateIt == StateMap.end()) {
            SkippedBlocks.push_back(B);
            if (isa<ReturnInst>(B->getTerminator())) {
                errs() << "All blocks: \n\t";
                for (auto *X: DFSOrderVec)
                    errs() << X->getName() << ", ";
                errs() << "\n";
                errs() << "Analyzed blocks: \n\t";
                for (auto *X: AnalyzedBlocks)
                    errs() << X->getName() << ", ";
                errs() << "\n";
                errs() << "Skipped blocks: \n\t";
                for (auto *X: SkippedBlocks)
                    errs() << X->getName() << ", ";
                errs() << "\n";
                llvm_unreachable("Error: Return block does not execute!");
            }
            // this block is not reachable in our analysis
            // call beforeVisit and afterVisit to deal with loops, and forward ProcessingBlockPointer
            beforeVisit(*B);
            afterVisit(*B);
            continue;
        }
        AnalyzedBlocks.push_back(B);
        auto &StateVec = StateIt->second;
        if (StateVec.empty()) {
            errs() << "All blocks: \n\t";
            for (auto *X: DFSOrderVec)
                errs() << X->getName() << ", ";
            errs() << "\n";
            errs() << "Analyzed blocks: \n\t";
            for (auto *X: AnalyzedBlocks)
                errs() << X->getName() << ", ";
            errs() << "\n";
            errs() << "Skipped blocks: \n\t";
            for (auto *X: SkippedBlocks)
                errs() << X->getName() << ", ";
            errs() << "\n";
            llvm_unreachable(("Error: no state found for " + B->getName()).str().c_str());
        } else if (StateVec.size() == 1) {
            ES = StateVec[0];
        } else {
            DEBUG_FUNC(&F, {
                dbgs() << "************************************\n";
                dbgs() << "Try to merge before " << B->getName() << "\n";
                dbgs() << "************************************\n";
                for (auto *State: StateVec)
                    if (State) dbgs() << *State << "\n*******\n\n";
            });

            ES = new ExecutionState;
            ES->merge(B, ++MergeID, StateVec, MergeCondMap[B]);
            assert(!FLI->isLoopHeader(B));

            DEBUG_FUNC(&F, {
                dbgs() << "************************************\n";
                dbgs() << "After merging ... \n";
                dbgs() << "************************************\n";
                dbgs() << *ES << "\n";
            });

            for (auto *State: StateVec) delete State;
        }
        StateMap.erase(StateIt);
        if (B->begin()->getOpcode() != Instruction::PHI) MergeCondMap.erase(B);

        beforeVisit(*B);
        visit(B);

        if (succ_size(B) == 0) {
            if (!isa<ReturnInst>(B->getTerminator()) || CallStack.empty()) {
                delete ES;
            }
        } else if (succ_size(B) == 1) {
            auto *Succ = *succ_begin(B);
            auto *LatchLP = FLI->isLoopLatch(B);
            bool Latching = LatchLP && LatchLP == FLI->isLoopHeader(Succ);
            if (!Latching) propagate(B, Succ, ES);
        } else {
            auto *Term = B->getTerminator();
            for (unsigned I = 0; I < Term->getNumSuccessors(); ++I) {
                auto *Succ = Term->getSuccessor(I);
                auto *LatchLP = FLI->isLoopLatch(B);
                bool Latching = LatchLP && LatchLP == FLI->isLoopHeader(Succ);
                if (Latching) continue; // do not propagate from latch to header
                auto *ExitingLP = FLI->isLoopExiting(B);
                bool Exiting = ExitingLP && !ExitingLP->contains(Succ);
                if (Exiting) continue; // do not propagate from exiting to exit
                propagate(B, Succ, ES->fork(B, I, Exiting));
            }
        }
        afterVisit(*B);
        ES = nullptr;
    }

    // gc states before blocks that will not be analyzed
    for (; ProcessingBlockPointer < DFSOrderVec.size(); ++ProcessingBlockPointer) {
        auto *B = DFSOrderVec[ProcessingBlockPointer];
        auto StateIt = StateMap.find(B);
        if (StateIt == StateMap.end()) {
            continue;
        }
        auto &StateVec = StateIt->second;
        for (auto *State: StateVec) delete State;
    }
}

void Executor::beforeVisit(BasicBlock &B) {
    if (auto *LP = FLI->isLoopHeader(&B)) {
        if (!LoopStack.empty() && LoopStack.back()->getLoop() == LP) {
            // an old loop, to visit the loop body again, clear the state buffer
            for (auto *BlockInLoop: *LP) {
                auto It = StateMap.find(BlockInLoop);
                if (It != StateMap.end()) StateMap.erase(It);
            }
        } else {
            // a new loop
            LoopStack.push_back(new LoopSummaryAnalysis(LP, ES, MergeID, ++LoopAnalysisID));
        }
        // increase the trip count, start a new trip/iteration
        LoopStack.back()->incTripCount();

        // before analyzing a loop, clear all results of the previous iteration
        // we need to delay this procedure, if it contains phi, because phi needs value from the loop body
        if (B.begin()->getOpcode() != Instruction::PHI)
            for (auto *BlockInLoop: *LP)
                for (auto &InstInLoop: *BlockInLoop)
                    if (!InstInLoop.getType()->isVoidTy()) ES->registerDeallocate(&InstInLoop);
    }
}

void Executor::afterVisit(BasicBlock &B) {
    // LoopStack.back() collects results of the current block, does analysis, determine if loop analysis finishes
    if (ES && !LoopStack.empty()) {
        // note ES may be null, meaning that actually, we cannot reach the block
        LoopStack.back()->collect(&B, ES, MergeID);
    }

    LastProcessingBlockPointer = ProcessingBlockPointer;
    if (auto *LP = FLI->isLoopLatch(&B)) {
        assert(succ_size(&B) == 1);
        assert(*succ_begin(&B) == LP->getHeader());
        auto *TopLP = LoopStack.back();
        assert(TopLP->getLoop() == LP);
        if (ES && !TopLP->finish()) { // ES != NULL means we can reach this block
            // let's go back to visit the loop again
            auto It = LoopHeaderIdxMap.find(LP);
            assert(It != LoopHeaderIdxMap.end());
            ProcessingBlockPointer = It->second;
            // propagate latch to header
            auto *NextIterationInitialState = TopLP->getNextInitialState(ES);
            propagate(&B, LP->getHeader(), NextIterationInitialState);

            if (NextIterationInitialState != ES) {
                // we fall back to unrolling mode, thus we do not use ES
                // print some info of the loop, this is only printed once
                pardiff_WARN("[LOOP] Fail to summarize a loop and fall back to the unrolling mode...");
                auto Term = LP->getHeader()->getTerminator();
                if (Term->hasMetadata("dbg")) {
                    auto &DbgLoc = Term->getDebugLoc();
                    pardiff_WARN("[LOOP] ...Line " << DbgLoc.get()->getLine() << " @ " << DbgLoc.get()->getFilename());
                }
                // if the current ES is not used, it can be deleted
                delete ES;
                ES = nullptr;
            }
            // reset the merge id, so that in a summarizing mode,
            // we create the same merge id at the same merging point
            if (!LoopStack.back()->inUnrollingMode()) {
                MergeID = LoopStack.back()->getMergeID();
                LoopAnalysisID = LoopStack.back()->getLoopAnalysisID();
            }
        } else {
            // ES == null || TopLP.finish() == true, which means the latch is not reachable or the loop analysis completes
            // propagate exiting to exit, use the summarized exiting states, and collect info from this nested loop
            ExecutionState *OneExitState = nullptr;
            for (auto It = TopLP->exiting_state_begin(), E = TopLP->exiting_state_end(); It != E; ++It) {
                auto Exiting = It->first.first;
                auto Exit = Exiting->getTerminator()->getSuccessor(It->first.second);
                propagate(Exiting, Exit, It->second);
                if (!OneExitState) OneExitState = It->second;
            }
            // we only need to do the following once with a single exit state
            // because OneExitState is used to extract the register values in the nested loop,
            // which are the same across different exit states
            //
            // OneExitState = 0 means that the whole loop is not reachable, no need to call collect()
            if (LoopStack.size() >= 2 && OneExitState) LoopStack[LoopStack.size() - 2]->collect(TopLP, OneExitState);

            delete LoopStack.back();
            LoopStack.pop_back();
            ProcessingBlockPointer++;
        }
    } else {
        // common path
        ProcessingBlockPointer++;
    }
}

void Executor::propagate(BasicBlock *From, BasicBlock *To, ExecutionState *State) {
    if (!State)
        return;

    std::vector<ExecutionState *> &Vec = StateMap[To];
    if (auto *LP = FLI->isLoopHeader(To)) {
        // loop header always has one input state,
        // either from prehead or from latch
        Vec.resize(1);
        Vec[0] = State;
        return;
    }

    Instruction *FirstInst = &*To->begin();
    if (auto *Phi = dyn_cast<PHINode>(FirstInst)) {
        unsigned PredSize = pred_size(To);
        if (Vec.empty()) {
            Vec.resize(PredSize);
        }
        for (unsigned I = 0; I < Phi->getNumIncomingValues(); ++I) {
            if (From == Phi->getIncomingBlock(I) && !Vec[I]) {
                Vec[I] = State;
                return;
            }
        }
    }
    Vec.push_back(State);
}

void Executor::load(LoadInst *Load, AddressValue *Addr, AbstractValue *Result) {
    if (Addr->poison()) return;

    ScalarValue SV(Result->bytewidth());
    AddressValue AV;
    AbstractValue *TempDst = isa<ScalarValue>(Result) ? &SV : (AbstractValue *) &AV;

    z3::expr_vector ScalarValVec = Z3::vec();
    for (size_t K = 0, Sz = Addr->size(); K < Sz; ++K) {
        auto *BaseMem = Addr->base(K);
        if (!BaseMem) continue; // do not load from a null pointer
        _load(Load, TempDst, BaseMem, Addr->offset(K));
        if (TempDst == &AV) {
            Result->add(TempDst);
        } else if (!TempDst->poison()) {
            ScalarValVec.push_back(TempDst->value());
            if (EnableNaming && isa<MessageBuffer>(BaseMem)) {
                auto Name = getVariableName(Load);
                if (Name != UNKNOWN_NAME) {
                    ES->addPC(Z3::naming(TempDst->value(), Name.c_str()));
                }
            }
        }
        TempDst->mkpoison(); // reset for the next round
    }
    if (ScalarValVec.size() == 1) {
        Result->set(ScalarValVec[0]);
    } else if (ScalarValVec.size() > 1) {
        auto ResultExpr = Z3::ite(Z3::free_bool(), ScalarValVec[0], ScalarValVec[1]);
        for (int I = 2; I < ScalarValVec.size(); ++I) {
            ResultExpr = Z3::ite(Z3::free_bool(), ResultExpr, ScalarValVec[I]);
        }
    }
}

void Executor::_load(LoadInst *LdInst, AbstractValue *Dst, MemoryBlock *Base, const z3::expr &Offset) {
    uint64_t Off;
    if (!Z3::is_numeral_u64(Offset, Off)) {
        auto *MB = dyn_cast<MessageBuffer>(Base);
        assert(MB);
        assert(isa<ScalarValue>(Dst));
        // for little endian, we need to swap the bytes
        Dst->set(MB->at(Offset, Dst->bytewidth(), !DL::isBigEndian() && Dst->bytewidth() % 2 == 0));
        recordMemoryRead(LdInst, Base, Dst);
        return;
    }

    auto *FirstLoaded = ES->getValue(Base->at(Off), false);
    if (!FirstLoaded) return;
    if (isa<AddressValue>(Dst) && isa<AddressValue>(FirstLoaded)) {
        // we do not allow other types are loaded as pointer types
        Dst->assign((AddressValue *) FirstLoaded);
        recordMemoryRead(LdInst, Base, Dst);
    } else if (isa<ScalarValue>(Dst) && isa<ScalarValue>(FirstLoaded)) {
        auto TargetBytes = Dst->bytewidth();
        if (FirstLoaded->bytewidth() == TargetBytes) {
            Dst->assign(FirstLoaded);
            recordMemoryRead(LdInst, Base, Dst);
        } else if (FirstLoaded->bytewidth() > TargetBytes) {
            if (FirstLoaded->poison()) Dst->mkpoison();
            else Dst->set(Z3::extract(FirstLoaded->value(), TargetBytes * 8 - 1, 0));
            recordMemoryRead(LdInst, Base, Dst);
        } else if (FirstLoaded->bytewidth() == 1) {
            // we only allow bytes combination
            z3::expr RetExpr = FirstLoaded->value(); // the expr is always 1 byte and 8 bits
            Off += FirstLoaded->bytewidth();
            for (unsigned NumBytes = 1; NumBytes < TargetBytes; ++NumBytes) {
                auto NextLoaded = ES->getValue(Base->at(Off), false);
                if (!NextLoaded || NextLoaded->bytewidth() != 1) return;
                Off += NextLoaded->bytewidth();
                RetExpr = Z3::concat(RetExpr, NextLoaded->value());
            }
            assert(RetExpr.get_sort().bv_size() == TargetBytes * 8);
            Dst->set(RetExpr.simplify());

            if (isa<MessageBuffer>(Base) && !DL::isBigEndian() && Dst->bytewidth() % 2 == 0) {
                Dst->set(Z3::byteswap(Dst->value()));
            }
            recordMemoryRead(LdInst, Base, Dst);
        }
    }
}

void Executor::store(StoreInst *I, AddressValue *Addr, AbstractValue *V2S) {
    if (Addr->poison()) return;
    bool StrongUpdate = Addr->size() <= 1;

    for (auto K = 0; K < Addr->size(); ++K) {
        if (!Addr->base(K)) continue; // do not store to a null pointer
        _store(I, V2S, Addr->base(K), Addr->offset(K), Z3::free_bool(), StrongUpdate);
    }
}

void Executor::_store(StoreInst *I, AbstractValue *V2S, MemoryBlock *Base, const z3::expr &Offset, const z3::expr &Cond,
                      bool SU) {
    if (auto *MsgBuff = dyn_cast<MessageBuffer>(Base)) {
        if (isa<ScalarValue>(V2S))
            MsgBuff->store(V2S->value(), Offset);
        pardiff_WARN("Try to overwrite the data buffer via store!");
        return;
    }

    uint64_t Off;
    if (!Z3::is_numeral_u64(Offset, Off)) {
        llvm_unreachable("Error: memory with a symbolic offset is not a message buff!");
    }

    auto *DstKey = Base->at(Off);
    auto *Dst = ES->getValue(DstKey, true);
    if (isa_and_nonnull<AddressValue>(V2S) && isa_and_nonnull<AddressValue>(Dst)) {
        // we do not allow other types are loaded as pointer types
        if (SU) ((AddressValue *) Dst)->assign((AddressValue *) V2S);
        else Dst->add(V2S);
        recordMemoryWritten(I, Base, DstKey);
    } else if (isa_and_nonnull<ScalarValue>(Dst) && isa_and_nonnull<ScalarValue>(V2S)) {
        auto DstBytes = Dst->bytewidth();
        auto V2SBytes = V2S->bytewidth();

        unsigned BytesToWrite = V2SBytes;
        while (BytesToWrite > 0) {
            // write bytes
            if (V2S->poison()) Dst->mkpoison();
            else {
                z3::expr Orig = Dst->value();
                if (BytesToWrite >= DstBytes) {
                    unsigned High = BytesToWrite * 8 - 1;
                    unsigned Low = High + 1 - DstBytes * 8;
                    if (SU) {
                        Dst->set(Z3::extract(V2S->value(), High, Low));
                    } else {
                        Dst->set(Z3::ite(Cond, Z3::extract(V2S->value(), High, Low), Orig));
                    }
                } else {
                    unsigned High = BytesToWrite * 8 - 1;
                    unsigned Low = 0;
                    auto Bytes2Store = Z3::extract(V2S->value(), High, Low);
                    if (Dst->poison()) {
                        Bytes2Store = Z3::concat(Z3::bv_val(0, DstBytes * 8 - (High + 1)), Bytes2Store);
                    } else {
                        Bytes2Store = Z3::concat(Z3::extract(Orig, DstBytes * 8 - 1, BytesToWrite * 8), Bytes2Store);
                    }
                    if (SU) {
                        Dst->set(Bytes2Store);
                    } else {
                        Dst->set(Z3::ite(Cond, Bytes2Store, Orig));
                    }
                }
            }
            recordMemoryWritten(I, Base, DstKey);

            // update bytes to write
            if (BytesToWrite > DstBytes) {
                BytesToWrite = BytesToWrite - DstBytes;
            } else {
                break;
            }

            // go to the next memory unit
            Off += DstBytes;
            DstKey = Base->at(Off);
            if (!DstKey) break;
            Dst = ES->getValue(DstKey, true);
            DstBytes = Dst->bytewidth();
        }
    }
}

void Executor::memoryCopy(Instruction *I, AddressValue *Dst, AddressValue *Src, AbstractValue *Len) {
    int64_t LenInt;
    if (Len->int64(LenInt)) {
        if (LenInt == 0) return;
        assert(LenInt > 0);
        memoryCopy(I, Dst, Src, LenInt);
    } else if (Len->poison()) {
        memoryCopy(I, Dst, Src, 1);
    } else {
        memoryCopy(I, Dst, Src, Len->value());
    }
}

void Executor::memoryCopy(Instruction *I, AddressValue *Dst, AddressValue *Src, const z3::expr &Len) {
    if (Dst->poison() || Src->poison() || Dst->size() > 1 || Src->size() > 1) {
        Dst->mkpoison();
        return;
    }

    if (isa<MessageBuffer>(Dst->base(0))) {
        pardiff_WARN("Try to overwrite the data buffer via memcpy!");
        return;
    } else if (isa<MessageBuffer>(Src->base(0))) {
        pardiff_WARN("Try to memcpy the message buff of a variable length!");
        auto First = Src->base(0)->at(Src->offset(0))->value();
         //auto Last = Src->base(0)->at(Src->offset(0) + Len)->value();
        auto Last = Src->base(0)->at(Z3::add(Src->offset(0), Len - 1))->value();
        auto Name = getStructFieldName(I->getOperand(0));
        if (Name != UNKNOWN_NAME)
            ES->addPC(Z3::naming(Z3::concat(First.simplify(), Last.simplify()), Name.c_str()));
        return;
    } else {
        memoryCopy(I, Dst, Src, 1);
    }
}

static uint64_t normalizeLen(AddressValue *V, uint64_t Len) {
    auto Base = V->base(0);
    if (isa<MessageBuffer>(Base)) return Len;

    auto Offset = V->offset(0);
    uint64_t Off;
    if (!Z3::is_numeral_u64(Offset, Off)) {
        llvm_unreachable("Error: symbolic offset of a non-mb memory space");
    }

    uint64_t Bytes = 0;
    while (Bytes < Len) {
        auto *Pointee = Base->at(Off);
        if (!Pointee) {
            break;
        }
        Off += Pointee->bytewidth();
        Bytes += Pointee->bytewidth();
    }
    assert(Bytes != 0);
    return Bytes >= Len ? Len : Bytes;
}

void Executor::memoryCopy(Instruction *I, AddressValue *Dst, AddressValue *Src, uint64_t Len) {
    if (Dst->poison() || Src->poison() || Dst->size() > 1 || Src->size() > 1) {
        Dst->mkpoison();
        return;
    }

    Len = normalizeLen(Dst, Len);
    Len = normalizeLen(Src, Len);

    auto DstOffset = Dst->offset(0);
    auto SrcOffset = Src->offset(0);
    uint64_t DstOff, SrcOff;
    bool DstOffsetConst = Z3::is_numeral_u64(DstOffset, DstOff);
    bool SrcOffsetConst = Z3::is_numeral_u64(SrcOffset, SrcOff);
    if (DstOffsetConst && (SrcOffsetConst || isa<MessageBuffer>(Src->base(0)))) {
        auto SrcBase = Src->base(0);
        auto DstBase = Dst->base(0);
        auto *SrcVal = ES->getValue(SrcBase->at(SrcOffset), false);
        if (!SrcVal) llvm_unreachable("Error : buffer overflow found during memcpy!");
        auto *DstKey = DstBase->at(DstOff);
        auto *DstVal = ES->getValue(DstKey, true);
        if (!DstVal) llvm_unreachable("Error : buffer overflow found during memcpy!");
        unsigned RemainingBytesInSrc = SrcVal->bytewidth();
        unsigned RemainingBytesInDst = DstVal->bytewidth();
        unsigned BytesCopied = 0;
        std::vector<z3::expr> Ev;

        while (BytesCopied < Len) {
            unsigned SrcBytes = SrcVal->bytewidth();
            unsigned DstBytes = DstVal->bytewidth();

            unsigned BytesToCopy = RemainingBytesInSrc;
            if (BytesToCopy + BytesCopied > Len) BytesToCopy = Len - BytesCopied;
            if (BytesToCopy > RemainingBytesInDst) BytesToCopy = RemainingBytesInDst;

            if (SrcVal->getKind() != DstVal->getKind() || SrcVal->poison()) {
                // int2ptr / ptr2int
                DstVal->mkpoison();
            } else if (isa<AddressValue>(SrcVal) && isa<AddressValue>(DstVal)) {
                if (BytesToCopy == SrcBytes) {
                    DstVal->assign(SrcVal);
                } else {
                    llvm_unreachable("Error : mis-aligned addresses!");
                }
            } else if (isa<ScalarValue>(SrcVal) && isa<ScalarValue>(DstVal)
                       && DstVal->poison() && BytesToCopy == DstBytes && DstBytes == RemainingBytesInDst) {
                if (RemainingBytesInSrc == SrcBytes && BytesToCopy == RemainingBytesInSrc) {
                    DstVal->set(SrcVal->value());
                } else {
                    unsigned H = (BytesToCopy + SrcBytes - RemainingBytesInSrc) * 8 - 1;
                    unsigned L = (SrcBytes - RemainingBytesInSrc) * 8;
                    DstVal->set(Z3::extract(SrcVal->value(), H, L));
                }
            } else if (isa<ScalarValue>(SrcVal) && isa<ScalarValue>(DstVal)) {
                if (DstVal->poison()) {
                    // let's zero-init it.
                    DstVal->set(Z3::bv_val(0, DstVal->bytewidth() * 8));
                }
                Ev.clear();
                if (RemainingBytesInDst - BytesToCopy > 0) {
                    unsigned H = DstBytes * 8 - 1;
                    unsigned L = (BytesToCopy + DstBytes - RemainingBytesInDst) * 8;
                    Ev.push_back(Z3::extract(DstVal->value(), H, L));
                }
                if (RemainingBytesInSrc == SrcBytes && BytesToCopy == RemainingBytesInSrc) {
                    Ev.push_back(SrcVal->value());
                } else {
                    unsigned H = (BytesToCopy + SrcBytes - RemainingBytesInSrc) * 8 - 1;
                    unsigned L = (SrcBytes - RemainingBytesInSrc) * 8;
                    Ev.push_back(Z3::extract(SrcVal->value(), H, L));
                }
                if (DstBytes - RemainingBytesInDst > 0) {
                    Ev.push_back(Z3::extract(DstVal->value(), DstBytes * 8 - RemainingBytesInDst * 8 - 1, 0));
                }
                assert(!Ev.empty());
                auto Res = Ev[0];
                for (unsigned K = 1; K < Ev.size(); ++K) {
                    Res = Z3::concat(Res, Ev[K]);
                }
                DstVal->set(Res);
            } else {
                // unknown cases
                DstVal->mkpoison();
            }
            recordMemoryWritten(I, DstBase, DstKey);

            // for next round
            BytesCopied += BytesToCopy;
            RemainingBytesInSrc = RemainingBytesInSrc - BytesToCopy;
            RemainingBytesInDst = RemainingBytesInDst - BytesToCopy;
            if (RemainingBytesInSrc == 0) {
                SrcOffset = Z3::add(SrcOffset, Z3::bv_val(SrcVal->bytewidth(), SrcOffset.get_sort().bv_size()));
                SrcVal = ES->getValue(SrcBase->at(SrcOffset), false);
                if (!SrcVal) {
                    assert(BytesCopied >= Len);
                    break;
                }
                RemainingBytesInSrc = SrcVal->bytewidth();
            }
            if (RemainingBytesInDst == 0) {
                DstOff += DstVal->bytewidth();
                DstKey = DstBase->at(DstOff);
                DstVal = ES->getValue(DstKey, true);
                if (!DstVal) {
                    assert(BytesCopied >= Len);
                    break;
                }
                RemainingBytesInDst = DstVal->bytewidth();
            }
        }
    }
}

static bool findLen(const z3::expr &Expr) {
    if (Z3::is_phi(Expr)) {
        // we only care about the value, not the condition
        for (int K = 0; K < Expr.num_args(); ++K) {
            if (!findLen(Expr.arg(K)))
                return false;
        }
        return true;
    } else if (Expr.is_ite()) {
        // we only care about the value, not the condition
        return findLen(Expr.arg(1)) && findLen(Expr.arg(2));
    }

    std::set<unsigned> Visited;
    z3::expr_vector Stack = Z3::vec();
    Stack.push_back(Expr);
    while (!Stack.empty()) {
        auto Top = Stack.back();
        Stack.pop_back();
        auto TopID = Z3::id(Top);
        if (Visited.count(TopID)) {
            continue;
        }
        Visited.insert(TopID);
        if (Top.decl().decl_kind() == Z3_OP_SELECT) {
            continue;
        }
        if (Z3::is_length(Top)) {
            return true;
        }
        auto NumArgs = Top.num_args();
        for (unsigned I = 0; I < NumArgs; ++I) {
            Stack.push_back(Top.arg(I));
        }
    }
    return false;
}

bool Executor::compareLength(ICmpInst *I) {
    if (!LengthSolution.getValue())
        return false;

    auto *Op1 = I->getOperand(0);
    auto *Op2 = I->getOperand(1);
    auto *P1 = ES->boundValue(I->getOperand(0));
    auto *P2 = ES->boundValue(I->getOperand(1));
    if (P1->poison() || P2->poison())
        return false;
    //llvm::slice_Inst.insert(I); 
    bool P1HasLen = findLen(P1->value());
    bool P2HasLen = findLen(P2->value());
    if (P1HasLen == P2HasLen)
        return false;

    auto *Result = ES->registerAllocate(I);
    switch (I->getPredicate()) {
        case CmpInst::ICMP_EQ:
        case CmpInst::ICMP_NE:
            return false; // keep the condition and do not use this heuristics
        case CmpInst::ICMP_UGE:
            if (P1HasLen) {
                ES->addPC(Z3::uge(P1->value(), P2->value()));
                Result->set(Z3::bv_val(1, 8)); // f(len) >= * must be true
                return true;
            }
            break;
        case CmpInst::ICMP_SGE:
            if (P1HasLen) {
                ES->addPC(Z3::sge(P1->value(), P2->value()));
                Result->set(Z3::bv_val(1, 8)); // f(len) >= * must be true
                return true;
            }
            break;
        case CmpInst::ICMP_UGT:
            if (P2HasLen) {
                ES->addPC(Z3::ule(P1->value(), P2->value()));
                Result->set(Z3::bv_val(0, 8)); // * > f(len) must be false
                return true;
            }
            break;
        case CmpInst::ICMP_SGT:
            if (P2HasLen) {
                ES->addPC(Z3::sle(P1->value(), P2->value()));
                Result->set(Z3::bv_val(0, 8)); // * > f(len) must be false
                return true;
            }
            break;
        case CmpInst::ICMP_ULT:
            if (P1HasLen) {
                ES->addPC(Z3::uge(P1->value(), P2->value()));
                Result->set(Z3::bv_val(0, 8)); // f(len) < * must be false
                return true;
            }
            break;
        case CmpInst::ICMP_SLT:
            if (P1HasLen) {
                ES->addPC(Z3::sge(P1->value(), P2->value()));
                Result->set(Z3::bv_val(0, 8)); // f(len) < * must be false
                return true;
            }
            break;
        case CmpInst::ICMP_ULE:
            if (P2HasLen) {
                ES->addPC(Z3::ule(P1->value(), P2->value()));
                Result->set(Z3::bv_val(1, 8)); // * <= f(len) must be true
                return true;
            }
            break;
        case CmpInst::ICMP_SLE:
            if (P2HasLen) {
                ES->addPC(Z3::sle(P1->value(), P2->value()));
                Result->set(Z3::bv_val(1, 8)); // * <= f(len) must be true
                return true;
            }
            break;
        default:
            llvm_unreachable("Error: wrong predicate for cmp!");
    }
    return false;
}

void Executor::packing(ReturnInst &I) {
    if (!AssertionPacking.getValue()) return;

    z3::expr_vector Args = Z3::vec();
    if (!packable(I, Args)) return;

    // pack pc
    auto Name = I.getFunction()->getName();
    if (ES->pcLength() > CallStack.back().PCSize) {
        auto NewPC = Z3::packing(("assertion_of_" + Name).str().c_str(), Args, 0);
        ES->replacePC(CallStack.back().PCSize, NewPC);
    }

    // pack ret
    if (!I.getNumOperands()) return;
    auto RetAbsVal = ES->boundValue(I.getOperand(0));
    if (RetAbsVal->poison()) return; // no need to pack
    if (isa<AddressValue>(RetAbsVal)) return; // no need to pack
    uint64_t X;
    if (RetAbsVal->uint64(X)) return; // no need to pack
    RetAbsVal->set(Z3::packing(("return_of_" + Name).str().c_str(), Args, RetAbsVal->bytewidth() * 8));
}

bool Executor::packable(ReturnInst &RetInst, z3::expr_vector Args) {
    auto &CFrame = CallStack.back();
    auto EasyPC = [](const z3::expr &E) {
        unsigned Num = 0;
        std::vector<z3::expr> Vec;
        Vec.push_back(E);
        while (!Vec.empty()) {
            auto Top = Vec.back();
            Vec.pop_back();
            Num++;
            if (Num > 256) return false;
            for (unsigned K = 0; K < E.num_args(); ++K)
                Vec.push_back(E.arg(K));
        }
        return true;
    };

    // if not very complex, just keep them
    bool AllEasy = true;
    for (unsigned I = CFrame.PCSize; I < ES->pcLength(); ++I) {
        if (!EasyPC(ES->pc(I))) {
            AllEasy = false;
            break;
        }
    }
    if (AllEasy) return false;

    // if the resulting pc only relates to the input arg, pack it
    std::set<unsigned> ArgRelated;
    for (unsigned I = 0, ArgSz = RetInst.getFunction()->arg_size(); I < ArgSz; ++I) {
        auto *Arg = RetInst.getFunction()->getArg(I);
        if (Arg->getType()->isPointerTy()) continue;
        auto *ArgAbsVal = ES->boundValue(Arg);
        if (ArgAbsVal->poison()) continue;
        z3::expr_vector Selects = Z3::find_all(ArgAbsVal->value(), false, [](const z3::expr &E) {
            return E.decl().decl_kind() == Z3_OP_SELECT;
        });
        for (auto E: Selects)
            ArgRelated.insert(Z3::id(E));
        if (!Selects.empty())
            Args.push_back(ArgAbsVal->value());
    }
    if (ArgRelated.empty()) return false;

    for (unsigned I = CFrame.PCSize; I < ES->pcLength(); ++I) {
        z3::expr_vector Selects = Z3::find_all(ES->pc(I), false, [](const z3::expr &E) {
            return E.decl().decl_kind() == Z3_OP_SELECT;
        });
        for (auto E: Selects) {
            if (!ArgRelated.count(Z3::id(E))) {
                return false;
            }
        }
    }
    pardiff_INFO(RetInst.getFunction()->getName().str() + " is packed!");
    return true;
}

void Executor::initializeGlobals(Function &F) {
    if (!UseGlobal.getValue())
        return;
    std::set<Function *> FuncSet;
    std::vector<Function *> FuncStack;
    FuncStack.push_back(&F);
    while (!FuncStack.empty()) {
        auto *Top = FuncStack.back();
        FuncStack.pop_back();
        if (FuncSet.count(Top)) continue;
        FuncSet.insert(Top);
        for (auto &B: *Top) {
            for (auto &I: B) {
                if (auto *CI = dyn_cast<CallInst>(&I)) {
                    if (auto *Callee = CI->getCalledFunction()) {
                        FuncStack.push_back(Callee);
                    }
                }
            }
        }
    }

    std::set<GlobalVariable *> GVSet;
    for (auto *Func: FuncSet) {
        for (auto &B: *Func) {
            for (auto &I: B) {
                for (unsigned K = 0; K < I.getNumOperands(); ++K) {
                    auto *Op = I.getOperand(K);
                    if (auto GV = dyn_cast<GlobalVariable>(Op)) {
                        if (!GV->isConstant() && GV->hasInitializer() &&
                            DL::getNumBytes(GV->getType()->getPointerElementType())) {
                            // constant are initialized on demand
                            GVSet.insert(GV);
                        }
                    }
                }
            }
        }
    }

    for (auto *GV: GVSet) {
        pardiff_INFO("Initializing global " + GV->getName().str() + "...");
        auto *GPtr = dyn_cast<AddressValue>(ES->registerAllocate(GV));
        assert(GPtr);
        auto GAddr = ES->heapAllocate(GV->getType()->getPointerElementType(), 1);
        GPtr->assign(GAddr);

        auto *Initializer = GV->getInitializer();
        std::vector<Constant *> FlattenedAbsValVec;
        DL::flatten(Initializer, FlattenedAbsValVec);
        auto Offset = 0;
        for (auto *Const: FlattenedAbsValVec) {
            AbstractValue *ConstAV = nullptr;
            if (Const->getType()->isPointerTy()) {
                ConstAV = new AddressValue;
            } else {
                ConstAV = new ScalarValue(DL::getNumBytes(Const->getType()));
            }
            assert(GAddr->at(Offset)->bytewidth() == ConstAV->bytewidth());
            _store(nullptr, ConstAV, GAddr, Z3::bv_val(Offset, DL::getPointerNumBytes() * 8), Z3::free_bool(), true);
            Offset += ConstAV->bytewidth();
        }
    }
}

void Executor::naming(Function *F, Value *Val, DIVariable *DIV) {
    // prepare the abstract address value
    auto *AbsVal = ES->boundValue(Val);
    auto *AddrVal = dyn_cast_or_null<AddressValue>(AbsVal);
    if (!AddrVal) return;
    if (AddrVal->size() != 1 || !isa_and_nonnull<MessageBuffer>(AddrVal->base(0))) return;

    // prepare the composite type
    if (!DIV) return;
    auto *Ty = DIV->getType();
    if (!Ty) return;
    Ty = DL::stripDITypeCast(Ty);
    if (!isa_and_nonnull<DIDerivedType>(Ty) || Ty->getTag() != dwarf::DW_TAG_pointer_type) return;
    Ty = DL::stripDITypeCast(((DIDerivedType *) Ty)->getBaseType());
    if (!isa_and_nonnull<DICompositeType>(Ty) || Ty->getTag() != dwarf::DW_TAG_structure_type) return;
    auto *CompositeTy = (DICompositeType *) Ty;
    if (CompositeTy->getName().empty()) return;
    std::vector<CompositeTypeElement> FlattenedTyVec;
    DL::flatten(CompositeTy, FlattenedTyVec);

    DEBUG_FUNC(F, {
        dbgs() << "struct " << CompositeTy->getName() << " {\n";
        for (auto &E: FlattenedTyVec) {
            dbgs() << "    " << E.FieldName << " @ " << E.FieldBitwidth << " @ " << E.FieldOffset << "\n";
        }
        dbgs() << "}\n";
    });

    auto Addr = AddrVal->base(0);
    auto *Mem = (MessageBuffer *) Addr;
    unsigned OffsetBvSz = AddrVal->offset(0).get_sort().bv_size();
    auto BaseIndex = AddrVal->offset(0);

    for (unsigned I = 0; I < FlattenedTyVec.size(); ++I) {
        auto &StructField = FlattenedTyVec[I];
        auto &FieldName = StructField.FieldName;
        auto FieldOffset = StructField.FieldOffset;
        auto FieldSize = StructField.FieldBitwidth;
        if (FieldSize == 0) continue; // sometimes we have 0-sized member, e.g., char a[0], in a struct
        assert(FieldSize % 8 == 0);

        auto StartIndex = Z3::add(BaseIndex, Z3::bv_val(FieldOffset / 8, OffsetBvSz));
        ES->addPC(Z3::naming(Mem->at(StartIndex, FieldSize / 8), FieldName.c_str()));
    }
}

void Executor::inferDITypePHI(PHINode &I) {
    auto It = ValueDebugTypeMap.find(&I);
    if (It != ValueDebugTypeMap.end()) return;
    for (unsigned K = 0; K < I.getNumIncomingValues(); ++K) {
        auto ValK = I.getIncomingValue(K);
        It = ValueDebugTypeMap.find(ValK);
        if (It != ValueDebugTypeMap.end()) {
            ValueDebugTypeMap[&I] = It->second;
            break;
        }
    }
}

void Executor::inferDITypeBitCast(BitCastInst &I) {
    auto It = ValueDebugTypeMap.find(&I);
    if (It != ValueDebugTypeMap.end()) return;
    auto ValK = I.getOperand(0);
    It = ValueDebugTypeMap.find(ValK);
    if (It != ValueDebugTypeMap.end()) {
        ValueDebugTypeMap[&I] = It->second;
    }
}

void Executor::inferDITypeSelect(SelectInst &I) {
    auto It = ValueDebugTypeMap.find(&I);
    if (It != ValueDebugTypeMap.end()) return;
    for (unsigned K = 1; K < I.getNumOperands(); ++K) {
        auto ValK = I.getOperand(K);
        It = ValueDebugTypeMap.find(ValK);
        if (It != ValueDebugTypeMap.end()) {
            ValueDebugTypeMap[&I] = It->second;
            break;
        }
    }
}

void Executor::inferDITypeLoad(LoadInst &I) {
    auto It = ValueDebugTypeMap.find(&I);
    if (It != ValueDebugTypeMap.end()) return;
    auto Val = I.getOperand(0);
    It = ValueDebugTypeMap.find(Val);
    if (It != ValueDebugTypeMap.end()) {
        auto *PtrTy = dyn_cast_or_null<DIDerivedType>(DL::stripDITypeCast(It->second));
        if (PtrTy && PtrTy->getTag() == dwarf::DW_TAG_pointer_type) {
            if (auto *DerefTy = DL::stripDITypeCast(PtrTy->getBaseType()))
                ValueDebugTypeMap[&I] = DerefTy;
        }
    }
}

void Executor::inferDITypeGEP(GetElementPtrInst &I) {
    auto TyIt = ValueDebugTypeMap.find(&I);
    if (TyIt != ValueDebugTypeMap.end()) return;

    // iterate the gep inst
    auto *PointerOp = I.getPointerOperand();
    TyIt = ValueDebugTypeMap.find(PointerOp);
    if (TyIt == ValueDebugTypeMap.end()) return;
    DIType *CurrDITy = DL::stripDITypeCast(TyIt->second);
    if (!CurrDITy || CurrDITy->getTag() != dwarf::DW_TAG_pointer_type) return;

    for (auto It = I.idx_begin(), E = I.idx_end(); It != E; ++It) {
        Value *IndexVal = It->get();
        int64_t Idx = -1;
        if (auto CI = dyn_cast<ConstantInt>(IndexVal)) {
            Idx = CI->getSExtValue();
        } else {
            auto IndexAbsVal = ES->boundValue(IndexVal);
            int64_t X;
            if (IndexAbsVal->int64(X)) Idx = X;
        }

        // update type
        if (CurrDITy->getTag() == dwarf::DW_TAG_pointer_type) {
            auto *DerivedTy = dyn_cast<DIDerivedType>(CurrDITy);
            assert(DerivedTy);
            CurrDITy = DL::stripDITypeCast(DerivedTy->getBaseType());
            if (!CurrDITy) return;
        } else if (CurrDITy->getTag() == dwarf::DW_TAG_array_type) {
            auto *CompositeTy = dyn_cast<DICompositeType>(CurrDITy);
            assert(CompositeTy);
            CurrDITy = dyn_cast<DIType>(CompositeTy->getBaseType());
            assert(CurrDITy);
            CurrDITy = DL::stripDITypeCast(CurrDITy);
            if (!CurrDITy) return;
        } else if (CurrDITy->getTag() == dwarf::DW_TAG_structure_type) {
            assert(Idx >= 0);
            auto *CompositeTy = dyn_cast<DICompositeType>(CurrDITy);
            assert(CompositeTy);
            if (Idx >= CompositeTy->getElements().size())
                return; // this may happen when one value are used as multiple diff types
            CurrDITy = dyn_cast<DIType>(CompositeTy->getElements()->getOperand(Idx).get());
            assert(CurrDITy);
            assert(CurrDITy->getTag() == dwarf::DW_TAG_member);
            CurrDITy = DL::stripDITypeCast(((DIDerivedType *) CurrDITy)->getBaseType());
            if (!CurrDITy) return;
        } else {
            // other unknown or complex cases, e.g., DW_TAG_union_type
            return;
        }
    }
    ValueDebugTypeMap[&I] = DL::getDIPointerType(CurrDITy);
}

std::string Executor::getStructFieldName(Value *Val) {
    auto *GEP = dyn_cast<GetElementPtrInst>(Val);
   if (!GEP) {
         if (auto *Load = dyn_cast<LoadInst>(Val)) return getStructFieldName(Load->getPointerOperand());
         else if (auto *Cast = dyn_cast<CastInst>(Val)) return getStructFieldName(Cast->getOperand(0));
         else return UNKNOWN_NAME;
     }

    std::vector<GetElementPtrInst *> GEPVec;
    while (GEP) {
        GEPVec.push_back(GEP);
        GEP = dyn_cast<GetElementPtrInst>(GEP->getPointerOperand());
    }
    std::reverse(GEPVec.begin(), GEPVec.end());

    std::vector<unsigned> IndexVec;
    for (auto *G: GEPVec) {
        // go through the indices, use 0 for array type
        auto *CurrType = G->getPointerOperandType()->getPointerElementType();
        auto IndexIt = G->idx_begin();
        IndexIt++;
        for (auto IndexEnd = G->idx_end(); IndexIt != IndexEnd; ++IndexIt) {
            auto *IndexVal = IndexIt->get();
            if (isa<StructType>(CurrType)) {
                auto *ConstantIndex = dyn_cast<ConstantInt>(IndexVal);
                if (!ConstantIndex) {
                     IndexVec.push_back(0);
                     pardiff_WARN("Struct type " << CurrType->getStructName() << " has a variable index!");
                     continue;
                 }
                auto CI = ConstantIndex->getSExtValue();
                if (CI < 0) {
                     IndexVec.push_back(0);
                     pardiff_WARN("Struct type " << CurrType->getStructName() << " has a negative index!");
                     continue;
                 }
                IndexVec.push_back(CI);
            } else {
                IndexVec.push_back(0);
            }
        }
    }

    // now GEP is the top level GEP
    GEP = GEPVec.front();
    auto *GEPPointer = GEP->getPointerOperand();
    auto *GEPPointerType = GEPPointer->getType();
    auto *GEPPointerElementType = GEPPointerType->getPointerElementType();
    if (!GEPPointerElementType->isStructTy()) return UNKNOWN_NAME;

    auto TyIt = ValueDebugTypeMap.find(GEPPointer);
    if (TyIt == ValueDebugTypeMap.end()) return UNKNOWN_NAME;
    DIType *CurrDITy = DL::stripDITypeCast(TyIt->second);
    if (!CurrDITy || CurrDITy->getTag() != dwarf::DW_TAG_pointer_type) return UNKNOWN_NAME;
    DIType *CompositeDITy = DL::stripDITypeCast(((DIDerivedType *) CurrDITy)->getBaseType());
    if (!CompositeDITy) return UNKNOWN_NAME;

    // now let us try to generate the field name
    std::string Name = CompositeDITy->getName().str();
    if (Name.empty()) return UNKNOWN_NAME; // this is a completely anonymous type

    CurrDITy = CompositeDITy;
    for (unsigned Index: IndexVec) {
        if (CurrDITy->getTag() == dwarf::DW_TAG_structure_type) {
            assert(Index >= 0);
            auto *CompositeTy = dyn_cast<DICompositeType>(CurrDITy);
            assert(CompositeTy);
            auto *MemTy = dyn_cast<DIType>(CompositeTy->getElements()->getOperand(Index).get());
            assert(MemTy);
            assert(MemTy->getTag() == dwarf::DW_TAG_member);

            // find the member and mv to the next type
             Name.append(".").append(MemTy->getName().str());
             CurrDITy = dyn_cast<DIDerivedType>(MemTy)->getBaseType();
             CurrDITy = DL::stripDITypeCast(CurrDITy);
             assert(CurrDITy);
        } else if (CurrDITy->getTag() == dwarf::DW_TAG_class_type) {
             assert(Index >= 0);
             auto *CompositeTy = dyn_cast<DICompositeType>(CurrDITy);
             assert(CompositeTy);

             dbgs() << *CompositeTy << "\n";

             DIType *MemTy = nullptr;

             auto *FirstElmt = CompositeTy->getElements()->getOperand(0).get();
             if (isa<DIDerivedType>(FirstElmt) && ((DIDerivedType *) FirstElmt)->getTag() == dwarf::DW_TAG_inheritance) {
                 auto *ParentClass = dyn_cast<DIDerivedType>(FirstElmt)->getBaseType();
                 assert(ParentClass);
                 dbgs() << *ParentClass << "\n";

                 DICompositeType *ParentClassDIC = dyn_cast<DICompositeType>(DMA->getRep(ParentClass));
                 assert(ParentClassDIC);
                 dbgs() << *ParentClassDIC << "\n";

                 MemTy = dyn_cast<DIType>(ParentClassDIC->getElements()->getOperand(Index).get());
                 assert(MemTy);
                 assert(MemTy->getTag() == dwarf::DW_TAG_member);
                 dbgs() << *MemTy << "\n";
             } else {
                 MemTy = dyn_cast<DIType>(CompositeTy->getElements()->getOperand(Index).get());
             }
            // find the member and mv to the next type
            Name.append(".").append(MemTy->getName().str());
            CurrDITy = dyn_cast<DIDerivedType>(MemTy)->getBaseType();
            CurrDITy = DL::stripDITypeCast(CurrDITy);
            assert(CurrDITy);
        } else {
            // we do not go into an array for naming
            break;
        }
    }
    return Name;
}

bool Executor::getBytes2Name(const z3::expr &Expr, z3::expr_vector &Vec) {
    // to find a single byte, a concatenation of a few bytes, or some simple ops (cast or binop) on the bytes
    // if the bytes have been named, we do not include them

    std::set<unsigned> Added2Vec;
    std::set<unsigned> Visited;
    std::vector<z3::expr> Stack;
    Stack.push_back(Expr);
    while (!Stack.empty()) {
        auto Top = Stack.back();
        auto TopID = Z3::id(Top);
        Visited.insert(TopID);
        Stack.pop_back();

        auto Decl = Top.decl();
        if (Decl.decl_kind() == Z3_OP_SELECT) {
            // a byte
            if (!ES->named(TopID) && !Added2Vec.count(TopID)) {
                Added2Vec.insert(TopID);
                Vec.push_back(Top);
            }
            continue;
        } else if (Decl.decl_kind() == Z3_OP_CONCAT) {
            // concatenation of bytes
            auto Seq = Z3::vec();
            if (isByteSeq(Top, &Seq)) {
                for (auto B: Seq) {
                    auto BID = Z3::id(B);
                    if (!ES->named(BID) && !Added2Vec.count(BID)) {
                        Added2Vec.insert(BID);
                        Vec.push_back(B);
                    }
                }
                continue;
            }
        } else if (Z3::is_phi(Top)) {
            bool HasBytes = false;
            for (unsigned K = 0; K < Top.num_args(); ++K) {
                auto PhiVal = Top.arg(K);
                if (isByteSeq(PhiVal)) {
                    HasBytes = true;
                    break;
                }
            }
            if (HasBytes) {
                Vec.push_back(Top);
            }
            continue;
        }

        for (unsigned K = 0; K < Top.num_args(); ++K) {
            auto E = Top.arg(K);
            if (Visited.count(Z3::id(E))) continue;
            Stack.push_back(E);
        }
    }

    return !Vec.empty();
}

std::string Executor::getVariableName(Instruction *I) {
    if (I->hasName())
        return I->getName().str();
    auto NextI = dyn_cast_or_null<DbgValueInst>(I->getNextNode());
    if (NextI && NextI->getValue() == I) {
        if (auto DIVar = NextI->getVariable()) {
            auto Name = DIVar->getName();
            if (!Name.empty())
                return Name.str();
        }
    }
    return UNKNOWN_NAME;
}

bool Executor::hasPhi(BasicBlock *B) const {
    // llvm language reference: PHI instructions must be first in a basic block.
    return isa<PHINode>(*B->begin());
}
