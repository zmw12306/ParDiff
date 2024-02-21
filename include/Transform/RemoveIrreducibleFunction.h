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

#ifndef TRANSFORM_REMOVEIRREDUCIBLEFUNCTION_H
#define TRANSFORM_REMOVEIRREDUCIBLEFUNCTION_H

#include <llvm/IR/Module.h>
#include <llvm/Pass.h>

#include <map>
#include <set>
#include <stack>
#include <vector>

using namespace llvm;

class CFGNode {
    friend class CFG;

private:
    std::set<CFGNode *> Preds;
    std::set<CFGNode *> Succs;
    std::vector<BasicBlock *> Blocks;

public:
    CFGNode() = default;

    ~CFGNode() = default;

    typedef std::set<CFGNode *>::iterator iterator;
    typedef std::set<CFGNode *>::const_iterator const_iterator;

    inline iterator begin() { return Succs.begin(); }

    inline iterator end() { return Succs.end(); }

    inline const_iterator begin() const { return Succs.begin(); }

    inline const_iterator end() const { return Succs.end(); }

    inline iterator pred_begin() { return Preds.begin(); }

    inline iterator pred_end() { return Preds.end(); }

    inline const_iterator pred_begin() const { return Preds.begin(); }

    inline const_iterator pred_end() const { return Preds.end(); }

    inline BasicBlock *operator[](size_t Index) const { return Blocks[Index]; }

    inline size_t numBlocks() { return Blocks.size(); }

    inline void addBlock(BasicBlock *B) { Blocks.push_back(B); }

    inline bool countPred(CFGNode *N) const { return Preds.count(N); }

    inline bool countSucc(CFGNode *N) const { return Succs.count(N); }
};

class CFG {
private:
    std::map<BasicBlock *, CFGNode *> BlockNodeMap;
    std::set<CFGNode *> Nodes;
    CFGNode *Entry;

public:
    CFG(Function &);

    ~CFG();

    typedef std::set<CFGNode *>::iterator iterator;
    typedef std::set<CFGNode *>::const_iterator const_iterator;

    inline iterator begin() { return Nodes.begin(); }

    inline iterator end() { return Nodes.end(); }

    inline const_iterator begin() const { return Nodes.begin(); }

    inline const_iterator end() const { return Nodes.end(); }

    inline size_t size() { return Nodes.size(); }

    inline CFGNode *getEntry() const { return Entry; }

    inline CFGNode *operator[](BasicBlock *BB) const {
        auto Iter = BlockNodeMap.find(BB);
        assert(Iter != BlockNodeMap.end() && "block does not have a shadow node!");
        return Iter->second;
    }

    void t1t2();

    void t1();

    void t2();

    friend raw_ostream &operator<<(raw_ostream &, const CFG &) LLVM_ATTRIBUTE_USED;
};

raw_ostream &operator<<(raw_ostream &, const CFG &) LLVM_ATTRIBUTE_USED;

class RemoveIrreducibleFunction : public FunctionPass {
public:
    static char ID;

    RemoveIrreducibleFunction();

    ~RemoveIrreducibleFunction() override;

    void getAnalysisUsage(AnalysisUsage &) const override;

    bool runOnFunction(Function &) override;
};

#endif // TRANSFORM_REMOVEIRREDUCIBLEFUNCTION_H
