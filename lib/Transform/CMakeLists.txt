add_library(PPYTransform STATIC
        LowerConstantExpr.cpp
        LowerGlobalConstantArraySelect.cpp
        LowerSelect.cpp
        MergeReturn.cpp
        NameBlock.cpp
        RemoveDeadBlock.cpp
        RemoveIrreducibleFunction.cpp
        RemoveNoRetFunction.cpp
        SimplifyLatch.cpp
        )