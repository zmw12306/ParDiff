#ifndef CORE_DISTINCTMETADATAANALYSIS_H
#define CORE_DISTINCTMETADATAANALYSIS_H

#include <llvm/IR/Module.h>
#include <llvm/Pass.h>
#include <set>

using namespace llvm;

class DistinctMetadataAnalysis : public ModulePass {
private:
    std::set<MDNode *> MDSet;
    std::map<MDNode *, MDNode *> MDRepMap;

public:
    static char ID;

    DistinctMetadataAnalysis() : ModulePass(ID) {}

    ~DistinctMetadataAnalysis() override = default;

    void getAnalysisUsage(AnalysisUsage &) const override;

    bool runOnModule(Module &) override;

    MDNode *getRep(MDNode *);

private:
    void runOnFunction(Function &);

    void collectMetadata(MDNode *N);

    void mergeDupDICompositeType();
};

#endif //CORE_DISTINCTMETADATAANALYSIS_H