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

#ifndef SUPPORT_INSTRUCTIONVISITOR_H
#define SUPPORT_INSTRUCTIONVISITOR_H

#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/ErrorHandling.h>


namespace llvm {
inline std::set<Instruction *> Inst;
inline std::set<Instruction *> slice_Inst;
    // We operate on opaque instruction classes, so forward declare all instruction
    // types now...
    //
#define HANDLE_INST(NUM, OPCODE, CLASS)   class CLASS;

#include "llvm/IR/Instruction.def"

#define DELEGATE(CLASS_TO_VISIT) \
return static_cast<SubClass*>(this)-> \
visit##CLASS_TO_VISIT(static_cast<CLASS_TO_VISIT&>(I))


/// Base class for instruction visitors
///
/// Instruction visitors are used when you want to perform different actions
/// for different kinds of instructions without having to use lots of casts
/// and a big switch statement (in your code, that is).
///
/// To define your own visitor, inherit from this class, specifying your
/// new type for the 'SubClass' template parameter, and "override" visitXXX
/// functions in your class. I say "override" because this class is defined
/// in terms of statically resolved overloading, not virtual functions.
///
/// For example, here is a visitor that counts the number of malloc
/// instructions processed:
///
///  /// Declare the class.  Note that we derive from InstructionVisitor instantiated
///  /// with _our new subclasses_ type.
///  ///
///  struct CountAllocaVisitor : public InstructionVisitor<CountAllocaVisitor> {
///    unsigned Count;
///    CountAllocaVisitor() : Count(0) {}
///
///    void visitAllocaInst(AllocaInst &AI) { ++Count; }
///  };
///
///  And this class would be used like this:
///    CountAllocaVisitor CAV;
///    CAV.visit(function);
///    NumAllocas = CAV.Count;
///
/// The defined has 'visit' methods for Instruction, and also for BasicBlock,
/// Function, and Module, which recursively process all contained instructions.
///
/// Note that if you don't implement visitXXX for some instruction type,
/// the visitXXX method for instruction superclass will be invoked. So
/// if instructions are added in the future, they will be automatically
/// supported, if you handle one of their superclasses.
///
/// The optional second template argument specifies the type that instruction
/// visitation functions should return. If you specify this, you *MUST* provide
/// an implementation of visitInstruction though!.
///
/// Note that this class is specifically designed as a template to avoid
/// virtual function call overhead.  Defining and using an InstructionVisitor is just
/// as efficient as having your own switch statement over the instruction
/// opcode.
    template<typename SubClass>
    class InstructionVisitor {
        //===--------------------------------------------------------------------===//
        // Interface code - This is the public interface of the InstructionVisitor that you
        // use to visit instructions...
        //

    public:
        // Generic visit method - Allow visitation to all instructions in a range
        template<class Iterator>
        void visit(Iterator Start, Iterator End) {
            while (Start != End)
                static_cast<SubClass *>(this)->visit(*Start++);
        }

        // Define visitors for functions and basic blocks...
        //
        void visit(Module &M) {
            static_cast<SubClass *>(this)->visitModule(M);
        }

        void visit(Function &F) {
            static_cast<SubClass *>(this)->visitFunction(F);
        }

        void visit(BasicBlock &BB) {
            static_cast<SubClass *>(this)->visitBasicBlock(BB);
        }

        // Forwarding functions so that the user can visit with pointers AND refs.
        void visit(Module *M) { visit(*M); }

        void visit(Function *F) { visit(*F); }

        void visit(BasicBlock *BB) { visit(*BB); }

        void visit(Instruction *I) {
            return visit(*I);
        }

        void beforeVisit(Instruction &I) {}

        void afterVisit(Instruction &I) {}

        // visit - Finally, code to visit an instruction...
        //
        void visit(Instruction &I) {
            static_assert(std::is_base_of<InstructionVisitor, SubClass>::value,
                          "Must pass the derived type to this template!");
            static_cast<SubClass *>(this)->beforeVisit(I);

            switch (I.getOpcode()) {
                default:
                    llvm_unreachable("Unknown instruction type encountered!");
                    // Build the switch statement using the Instruction.def file...
#define HANDLE_INST(NUM, OPCODE, CLASS) \
case Instruction::OPCODE: { static_cast<SubClass*>(this)->visit##OPCODE(static_cast<CLASS&>(I)); \
static_cast<SubClass *>(this)->afterVisit(I); return; }

#include "llvm/IR/Instruction.def"
            }
        }

        //===--------------------------------------------------------------------===//
        // Visitation functions... these functions provide default fallbacks in case
        // the user does not specify what to do for a particular instruction type.
        // The default behavior is to generalize the instruction type to its subtype
        // and try visiting the subtype.  All of this should be inlined perfectly,
        // because there are no virtual functions to get in the way.
        //

        // When visiting a module, function or basic block directly, these methods get
        // called to indicate when transitioning into a new unit.
        //
        void visitModule(Module &M) {
            visit(M.begin(), M.end());
        }

        void visitFunction(Function &F) {
            visit(F.begin(), F.end());
        }

        void visitBasicBlock(BasicBlock &BB) {
            visit(BB.begin(), BB.end());
        }

        // Define instruction specific visitor functions that can be overridden to
        // handle SPECIFIC instructions.  These functions automatically define
        // visitMul to proxy to visitBinaryOperator for instance in case the user does
        // not need this generality.
        //
        // These functions can also implement fan-out, when a single opcode and
        // instruction have multiple more specific Instruction subclasses. The Call
        // instruction currently supports this. We implement that by redirecting that
        // instruction to a special delegation helper.
#define HANDLE_INST(NUM, OPCODE, CLASS) \
void visit##OPCODE(CLASS &I) { \
if (NUM == Instruction::Call) \
return delegateCallInst(I); \
else \
DELEGATE(CLASS); \
}

#include "llvm/IR/Instruction.def"

// Specific Instruction type classes... note that all of the casts are
// necessary because we use the instruction classes as opaque types...
//
        void visitICmpInst(ICmpInst &I) { DELEGATE(CmpInst); }

        void visitFCmpInst(FCmpInst &I) { DELEGATE(CmpInst); }

        void visitAllocaInst(AllocaInst &I) { DELEGATE(UnaryInstruction); }

        void visitLoadInst(LoadInst &I) { DELEGATE(UnaryInstruction); }

        void visitStoreInst(StoreInst &I) { DELEGATE(Instruction); }

        void visitAtomicCmpXchgInst(AtomicCmpXchgInst &I) { DELEGATE(Instruction); }

        void visitAtomicRMWInst(AtomicRMWInst &I) { DELEGATE(Instruction); }

        void visitFenceInst(FenceInst &I) { DELEGATE(Instruction); }

        void visitGetElementPtrInst(GetElementPtrInst &I) { DELEGATE(Instruction); }

        void visitPHINode(PHINode &I) { DELEGATE(Instruction); }

        void visitTruncInst(TruncInst &I) { DELEGATE(CastInst); }

        void visitZExtInst(ZExtInst &I) { DELEGATE(CastInst); }

        void visitSExtInst(SExtInst &I) { DELEGATE(CastInst); }

        void visitFPTruncInst(FPTruncInst &I) { DELEGATE(CastInst); }

        void visitFPExtInst(FPExtInst &I) { DELEGATE(CastInst); }

        void visitFPToUIInst(FPToUIInst &I) { DELEGATE(CastInst); }

        void visitFPToSIInst(FPToSIInst &I) { DELEGATE(CastInst); }

        void visitUIToFPInst(UIToFPInst &I) { DELEGATE(CastInst); }

        void visitSIToFPInst(SIToFPInst &I) { DELEGATE(CastInst); }

        void visitPtrToIntInst(PtrToIntInst &I) { DELEGATE(CastInst); }

        void visitIntToPtrInst(IntToPtrInst &I) { DELEGATE(CastInst); }

        void visitBitCastInst(BitCastInst &I) { DELEGATE(CastInst); }

        void visitAddrSpaceCastInst(AddrSpaceCastInst &I) { DELEGATE(CastInst); }

        void visitSelectInst(SelectInst &I) { DELEGATE(Instruction); }

        void visitVAArgInst(VAArgInst &I) { DELEGATE(UnaryInstruction); }

        void visitExtractElementInst(ExtractElementInst &I) { DELEGATE(Instruction); }

        void visitInsertElementInst(InsertElementInst &I) { DELEGATE(Instruction); }

        void visitShuffleVectorInst(ShuffleVectorInst &I) { DELEGATE(Instruction); }

        void visitExtractValueInst(ExtractValueInst &I) { DELEGATE(UnaryInstruction); }

        void visitInsertValueInst(InsertValueInst &I) { DELEGATE(Instruction); }

        void visitLandingPadInst(LandingPadInst &I) { DELEGATE(Instruction); }

        void visitFuncletPadInst(FuncletPadInst &I) { DELEGATE(Instruction); }

        void visitCleanupPadInst(CleanupPadInst &I) { DELEGATE(FuncletPadInst); }

        void visitCatchPadInst(CatchPadInst &I) { DELEGATE(FuncletPadInst); }

        void visitFreezeInst(FreezeInst &I) { DELEGATE(Instruction); }

// Handle the special instrinsic instruction classes.
        void visitDbgDeclareInst(DbgDeclareInst &I) { DELEGATE(DbgVariableIntrinsic); }

        void visitDbgValueInst(DbgValueInst &I) { DELEGATE(DbgVariableIntrinsic); }

        void visitDbgVariableIntrinsic(DbgVariableIntrinsic &I) { DELEGATE(DbgInfoIntrinsic); }

        void visitDbgLabelInst(DbgLabelInst &I) { DELEGATE(DbgInfoIntrinsic); }

        void visitDbgInfoIntrinsic(DbgInfoIntrinsic &I) { DELEGATE(IntrinsicInst); }

        void visitMemSetInst(MemSetInst &I) { DELEGATE(MemIntrinsic); }

        void visitMemCpyInst(MemCpyInst &I) { DELEGATE(MemTransferInst); }

        void visitMemMoveInst(MemMoveInst &I) { DELEGATE(MemTransferInst); }

        void visitMemTransferInst(MemTransferInst &I) { DELEGATE(MemIntrinsic); }

        void visitMemIntrinsic(MemIntrinsic &I) { DELEGATE(IntrinsicInst); }

        void visitVAStartInst(VAStartInst &I) { DELEGATE(IntrinsicInst); }

        void visitVAEndInst(VAEndInst &I) { DELEGATE(IntrinsicInst); }

        void visitVACopyInst(VACopyInst &I) { DELEGATE(IntrinsicInst); }

        void visitIntrinsicInst(IntrinsicInst &I) { DELEGATE(CallInst); }

        void visitCallInst(CallInst &I) { DELEGATE(CallBase); }

        void visitInvokeInst(InvokeInst &I) { DELEGATE(CallBase); }

        void visitCallBrInst(CallBrInst &I) { DELEGATE(CallBase); }

// While terminators don't have a distinct type modeling them, we support
// intercepting them with dedicated a visitor callback.
        void visitReturnInst(ReturnInst &I) {
            return static_cast<SubClass *>(this)->visitTerminator(I);
        }

        void visitBranchInst(BranchInst &I) {
            return static_cast<SubClass *>(this)->visitTerminator(I);
        }

        void visitSwitchInst(SwitchInst &I) {
            return static_cast<SubClass *>(this)->visitTerminator(I);
        }

        void visitIndirectBrInst(IndirectBrInst &I) {
            return static_cast<SubClass *>(this)->visitTerminator(I);
        }

        void visitResumeInst(ResumeInst &I) {
            return static_cast<SubClass *>(this)->visitTerminator(I);
        }

        void visitUnreachableInst(UnreachableInst &I) {
            return static_cast<SubClass *>(this)->visitTerminator(I);
        }

        void visitCleanupReturnInst(CleanupReturnInst &I) {
            return static_cast<SubClass *>(this)->visitTerminator(I);
        }

        void visitCatchReturnInst(CatchReturnInst &I) {
            return static_cast<SubClass *>(this)->visitTerminator(I);
        }

        void visitCatchSwitchInst(CatchSwitchInst &I) {
            return static_cast<SubClass *>(this)->visitTerminator(I);
        }

        void visitTerminator(Instruction &I) { DELEGATE(Instruction); }

// Next level propagators: If the user does not overload a specific
// instruction type, they can overload one of these to get the whole class
// of instructions...
//
        void visitCastInst(CastInst &I) { DELEGATE(UnaryInstruction); }

        void visitUnaryOperator(UnaryOperator &I) { DELEGATE(UnaryInstruction); }

        void visitBinaryOperator(BinaryOperator &I) { DELEGATE(Instruction); }

        void visitCmpInst(CmpInst &I) { DELEGATE(Instruction); }

        void visitUnaryInstruction(UnaryInstruction &I) { DELEGATE(Instruction); }

// The next level delegation for `CallBase` is slightly more complex in order
// to support visiting cases where the call is also a terminator.
        void visitCallBase(CallBase &I) {
            if (isa<InvokeInst>(I) || isa<CallBrInst>(I))
                return static_cast<SubClass *>(this)->visitTerminator(I);

            DELEGATE(Instruction);
        }

// If the user wants a 'default' case, they can choose to override this
// function.  If this function is not overloaded in the user's subclass, then
// this instruction just gets ignored.
//
// Note that you MUST override this function if your return type is not void.
//
        void visitInstruction(Instruction &I) {}  // Ignore unhandled instructions

    private:
        // Special helper function to delegate to CallInst subclass visitors.
        void delegateCallInst(CallInst &I) {
            if (const Function *F = I.getCalledFunction()) {
                switch (F->getIntrinsicID()) {
                    default:
                        DELEGATE(IntrinsicInst);
                    case Intrinsic::dbg_declare:
                        DELEGATE(DbgDeclareInst);
                    case Intrinsic::dbg_value:
                        DELEGATE(DbgValueInst);
                    case Intrinsic::dbg_label:
                        DELEGATE(DbgLabelInst);
                    case Intrinsic::memcpy:
                        DELEGATE(MemCpyInst);
                    case Intrinsic::memmove:
                        DELEGATE(MemMoveInst);
                    case Intrinsic::memset:
                        DELEGATE(MemSetInst);
                    case Intrinsic::vastart:
                        DELEGATE(VAStartInst);
                    case Intrinsic::vaend:
                        DELEGATE(VAEndInst);
                    case Intrinsic::vacopy:
                        DELEGATE(VACopyInst);
                    case Intrinsic::not_intrinsic:
                        break;
                }
            }
            DELEGATE(CallInst);
        }

        // An overload that will never actually be called, it is used only from dead
        // code in the dispatching from opcodes to instruction subclasses.
        void delegateCallInst(Instruction &I) {
            llvm_unreachable("delegateCallInst called for non-CallInst");
        }
    };

#undef DELEGATE

} // End llvm namespace

#endif //SUPPORT_INSTRUCTIONVISITOR_H
