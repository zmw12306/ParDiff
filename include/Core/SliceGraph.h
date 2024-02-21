/*
 *  pardiff lifts protocol source code in C to its specification in BNF
 *  Copyright (C) 2022  
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


#ifndef BNF_SLICEGRAPH_H
#define BNF_SLICEGRAPH_H
#include <queue>
#include "Support/Z3.h"
//#include "BNF/BNF.h"



class SliceGraph;

extern std::vector<z3::expr> graphsForDiff;
extern SliceGraph graph1;
extern SliceGraph graph2;
class SliceGraphNode {
    friend class SliceGraph;

private:
    /// @{
    z3::expr Condition;
    unsigned ConditionID;
    /// @}

    /// @{
    const char *Color;
    std::string Hint;
    /// @}

    std::set<SliceGraphNode *> Children;
    std::set<SliceGraphNode *> Parents;

public:

    SliceGraphNode(SliceGraphNode *node): Condition(node->getCondition()) {
        //this->Condition = node->getCondition();
        this->ConditionID = node->getConditionID();
        this->Color = node->getColor();
        this->Hint = node->getHint();
    }

    SliceGraphNode *deepcopy(){
        SliceGraphNode * New_node = new SliceGraphNode(this);
        for(std::set<SliceGraphNode *>::const_iterator i = this->child_begin(); i!=this->child_end();i++){
            SliceGraphNode * New_child = (*i)->deepcopy();
            New_node->addChild(New_child);
            New_child->addParent(New_node);
        }
        return New_node;
    }

    SliceGraphNode(z3::expr Cond) : Condition(Cond), ConditionID(Z3::id(Cond)), Color(0) {}
    
    z3::expr getCondition() const { return Condition; }

    void setCondition(const z3::expr &C) { Condition = C; }

    unsigned getConditionID() const { return ConditionID; };

    void setConditionID(unsigned ID) { ConditionID = ID; }

    const char *getColor() const { return Color; }

    void setColor(const char *C) { Color = C; }

    const std::string &getHint() const { return Hint; }

    void setHint(std::string H) { Hint = H; }

    void addChild(SliceGraphNode *N) { Children.insert(N); }

    void addParent(SliceGraphNode *N) { Parents.insert(N); }

    void clearChild() {Children.clear();}
    
    void clearParent() {Parents.clear();}

    unsigned getNumChildren() const { return Children.size(); }

    unsigned getNumParents() const { return Parents.size(); }

    std::set<SliceGraphNode *>::const_iterator child_begin() const { return Children.begin(); }

    std::set<SliceGraphNode *>::const_iterator child_end() const { return Children.end(); }

    std::set<SliceGraphNode *>::const_iterator parent_begin() const { return Parents.begin(); }

    std::set<SliceGraphNode *>::const_iterator parent_end() const { return Parents.end(); }

    std::set<SliceGraphNode *> find_exitschild() {
        std::set<SliceGraphNode *> res;
        std::vector<SliceGraphNode *> Stack;
        std::set<SliceGraphNode *> Visited;
        Stack.push_back(this);
        while (!Stack.empty()) {
            auto *Top = Stack.back();
            Stack.pop_back();
            if (Visited.count(Top)) continue;
            Visited.insert(Top);

            if(Top->getNumChildren()==0){
                res.insert(Top);
            }

            for (auto *Ch: Top->Children) {
                Stack.push_back(Ch);
            }
        }
        return res;
    }

    SliceGraphNode* findmaxSubgraph(std::set<SliceGraphNode *> diff_nodes){
        SliceGraphNode *node;
        if(diff_nodes.count(this)!=0){
            node = this->deepcopy();
        }
        else{
            node = new SliceGraphNode(this);
            for(std::set<SliceGraphNode *>::const_iterator i = this->child_begin(); i!=this->child_end();i++){
                SliceGraphNode * New_child = (*i)->findmaxSubgraph(diff_nodes);
                node->addChild(New_child);
                New_child->addParent(node);
            }
        }
        return node;
    }
    
};

class SliceGraph {
private:
    std::set<SliceGraphNode *> Entries;
    std::set<SliceGraphNode *> Exits;

public:
    ~SliceGraph();

    void dot(std::string &File, const char * = "") const;

    unsigned size() const;

    void simplifyBeforeSymbolicExecution();

    void simplifyAfterSymbolicExecution();

    void simplifyByRewriting();

    void simplifyByRemoving();

    void simplifyByMerging();

    void simplifyByHashConsing();

    std::set<SliceGraphNode *> & getEntries(){return Entries;}

    std::set<SliceGraphNode *> & getExits(){return Exits;}

    z3::expr pc();

    std::set<SliceGraphNode *>::iterator entry_begin() { return Entries.begin(); }

    std::set<SliceGraphNode *>::iterator entry_end() { return Entries.end(); }

    SliceGraph* findSubgraph(SliceGraphNode *node);


    template<class ActionAtDFS>
    void dfs(ActionAtDFS Act) const {
        std::vector<SliceGraphNode *> Stack;
        std::set<SliceGraphNode *> Visited;
        for (auto *En: Entries)
            Stack.push_back(En);
        while (!Stack.empty()) {
            auto *Top = Stack.back();
            Stack.pop_back();
            if (Visited.count(Top)) continue;
            Visited.insert(Top);

            Act(Top);

            for (auto *Ch: Top->Children) {
                Stack.push_back(Ch);
            }
        }
    }

private:
    z3::expr simplify(const z3::expr &) const;

    void remove(SliceGraphNode *, bool PreserveReachability);

    void remove(SliceGraphNode *, bool PreserveReachability, std::set<SliceGraphNode *> *Deleted);

    void postOrder(std::vector<SliceGraphNode *> &);

    void postOrder(SliceGraphNode *, std::set<SliceGraphNode *> &, std::vector<SliceGraphNode *> &);

    void topoOrder(std::vector<SliceGraphNode *> &);

    std::vector<z3::expr> merge(std::vector<std::vector<z3::expr>> &);

    void validate(SliceGraphNode *) const;

    void removeFrom(SliceGraphNode *, std::set<SliceGraphNode *> &Removed);


public:
    static SliceGraph *get(const z3::expr PC, bool AllExpanded = false);

    void dfs_findexits(){
        std::vector<SliceGraphNode *> Stack;
        std::set<SliceGraphNode *> Visited;
        for (auto *En: Entries)
            Stack.push_back(En);
            while (!Stack.empty()) {
                auto *Top = Stack.back();
                Stack.pop_back();
                if (Visited.count(Top)) continue;
                Visited.insert(Top);

                if(Top->getNumChildren()==0){
                    getExits().insert(Top);
                }

                for (auto *Ch: Top->Children) {
                    Stack.push_back(Ch);
                }
            }
    }


private:
    static SliceGraph *getAnd(const z3::expr &And);

    static SliceGraph *getOr(const z3::expr &Or);

    static SliceGraph *getUnknown(const z3::expr &Unk);

    static SliceGraph *getGraph(const z3::expr &Any);
};
//SliceGraph *getDiff(SliceGraph *first_graph, SliceGraph *second_graph);
#endif //BNF_SLICEGRAPH_H