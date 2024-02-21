#include <llvm/IR/Constants.h>
#include <llvm/IR/DebugInfoMetadata.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Metadata.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Support/Debug.h>
#include "Core/DistinctMetadataAnalysis.h"

#define DEBUG_TYPE "MergeDistinctMetadata"

char DistinctMetadataAnalysis::ID = 0;
static RegisterPass<DistinctMetadataAnalysis> X(DEBUG_TYPE, "merge distinct metadata");

void DistinctMetadataAnalysis::getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesAll();
}

bool DistinctMetadataAnalysis::runOnModule(Module &M) {
    // collect all metadata
    for (auto &F: M) {
        runOnFunction(F);
    }

    // merge duplicate DICompositeType
    mergeDupDICompositeType();
    return false;
}

void DistinctMetadataAnalysis::runOnFunction(Function &F) {
    SmallVector<std::pair<unsigned, MDNode *>, 4> MDForInst;
    for (auto &B: F) {
        for (auto &I: B) {
            // get the Metadata declared in the llvm intrinsic functions such as llvm.dbg.declare()
            if (CallInst *CI = dyn_cast<CallInst>(&I)) {
                if (Function *Callee = CI->getCalledFunction()) {
                    if (Callee->getName().startswith("llvm.")) {
                        for (unsigned K = 0, E = I.getNumOperands(); K != E; ++K) {
                            if (MetadataAsValue *N = dyn_cast_or_null<MetadataAsValue>(I.getOperand(K))) {
                                collectMetadata(dyn_cast<MDNode>(N->getMetadata()));
                            }
                        }
                    }
                }
            }

            // get all the md nodes attached to each instruction
            I.getAllMetadata(MDForInst);
            for (unsigned K = 0, E = MDForInst.size(); K != E; ++K) {
                collectMetadata(MDForInst[K].second);
            }
            MDForInst.clear();
        }
    }
}

void DistinctMetadataAnalysis::collectMetadata(MDNode *N) {
    if (!N) return;
    if (MDSet.count(N)) return;
    MDSet.insert(N);

    for (unsigned i = 0, e = N->getNumOperands(); i != e; ++i) {
        if (MDNode *Op = dyn_cast_or_null<MDNode>(N->getOperand(i))) {
            collectMetadata(Op);
        }
    }
}

void DistinctMetadataAnalysis::mergeDupDICompositeType() {
    std::map<std::tuple<std::string, DIFile *, unsigned, uint64_t, unsigned>, std::set<DICompositeType *>> Groups;

    for (auto *M: MDSet) {
        if (auto *CM = dyn_cast<DICompositeType>(M)) {
            auto Name = CM->getName().str();
            auto File = CM->getFile();
            auto Line = CM->getLine();
            auto Size = CM->getSizeInBits();
            auto Tag = CM->getTag();
            if (Tag != dwarf::DW_TAG_class_type) continue;

            Groups[std::make_tuple(Name, File, Line, Size, Tag)].insert(CM);
        }
    }

    auto It = Groups.begin();
    while (It != Groups.end()) {
        if (It->second.size() <= 1) {
            It = Groups.erase(It);
        } else {
            ++It;
        }
    }

    for (auto &GIt: Groups) {
        MDNode *Rep = nullptr;
        for (auto *M: GIt.second) {
            if (M->getElements().size()) {
                Rep = M;
                break;
            }
        }
        if (!Rep) continue;
        for (auto *M: GIt.second) {
            MDRepMap[M] = Rep;
        }
    }
}

MDNode *DistinctMetadataAnalysis::getRep(MDNode *M) {
    auto It = MDRepMap.find(M);
    if (It == MDRepMap.end())
        return M;
    else
        return It->second;
}