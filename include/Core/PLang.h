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


#ifndef P_PLANG_H
#define P_PLANG_H

#include "Core/SliceGraph.h"

#include <list>
#include <vector>

class FuncCode {
private:
    std::vector<std::string> CodeVec;

public:
    FuncCode &append(const std::string &S) {
        CodeVec.push_back(S);
        return *this;
    }

    friend raw_ostream &operator<<(llvm::raw_ostream &, const FuncCode &);
};

raw_ostream &operator<<(llvm::raw_ostream &, const FuncCode &);

class PLang {
private:
    std::list<FuncCode> FuncVec;
    std::map<SliceGraphNode *, std::string> ReentryCodeMap;

public:
    PLang(SliceGraph *);

    void dump(StringRef FileName);

private:
    void gen(SliceGraphNode *, FuncCode &Code, unsigned Indent, bool Enforce = false);

    std::string toString(const z3::expr &);

    std::string toStringDefault(const z3::expr &Expr);

    std::string toStringTemplate(const z3::expr &Expr, const char *Op);

    friend raw_ostream &operator<<(llvm::raw_ostream &, const PLang &);
};

raw_ostream &operator<<(llvm::raw_ostream &, const PLang &);

#endif //P_PLANG_H
