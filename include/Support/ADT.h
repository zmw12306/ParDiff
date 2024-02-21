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


#ifndef SUPPORT_ADT_H
#define SUPPORT_ADT_H

#include <vector>

class ADT {
public:
    /// return true if the first is a subsequence of the second
    template<class T, class Equal>
    static bool isSubsequence(const std::vector<T> &V1, const std::vector<T> &V2, Equal Eq) {
        return ADT::isSubsequence(V1, V2, V1.size(), V2.size(), Eq);
    }

    /// split a string into multiple lines
    static std::string autoNewLine(const std::string &Orig, unsigned LineLen, const char *NLSym = "\n") {
        SmallVector<StringRef> Splits;
        StringRef Ref(Orig);
        Ref.split(Splits, ' ');

        unsigned CurrentLineLen = 0;
        std::string Ret;
        for (auto Str: Splits) {
            if (Str.startswith("<<")) {
                Ret.append("\\<\\<");
                Str = Str.substr(2);
            } else if (Str.startswith(">>")) {
                Ret.append("\\>\\>");
                Str = Str.substr(2);
            } else if (Str.startswith("||")) {
                Ret.append("\\|\\|");
                Str = Str.substr(2);
            } else if (Str.startswith("<")) {
                Ret.append("\\<");
                Str = Str.substr(1);
            } else if (Str.startswith(">")) {
                Ret.append("\\>");
                Str = Str.substr(1);
            } else if (Str.startswith("|")) {
                Ret.append("\\|");
                Str = Str.substr(1);
            }

            Ret.append(Str.str()).append(" ");
            CurrentLineLen += Str.size();
            CurrentLineLen += 1;
            if (CurrentLineLen > LineLen) {
                CurrentLineLen = 0;
                Ret.append(NLSym).append("    ");
            }
        }
        return Ret;
    }

    template<class T, class Predicate>
    static bool forall(const std::vector<T> &S1, const std::vector<T> &S2, Predicate P) {
        for (auto &T1 : S1) {
            for (auto &T2 : S2) {
                if (!P(T1, T2)) return false;
            }
        }
        return true;
    }

    template<class T, class Predicate>
    static bool exists(const std::vector<T> &S1, const std::vector<T> &S2, Predicate P) {
        for (auto &T1 : S1) {
            for (auto &T2 : S2) {
                if (P(T1, T2)) return true;
            }
        }
        return false;
    }

private:
    template<class T, class Equal>
    static bool isSubsequence(const std::vector<T> &V1, const std::vector<T> &V2, unsigned K1, unsigned K2, Equal Eq) {
        // Base cases
        if (K1 == 0) return true;
        if (K2 == 0) return false;

        // If last elements of two vectors are matching
        if (Eq(V1[K1 - 1], V2[K2 - 1]))
            return isSubsequence(V1, V2, K1 - 1, K2 - 1, Eq);

        // If last elements are not matching
        return isSubsequence(V1, V2, K1, K2 - 1, Eq);
    }
};

#endif //SUPPORT_ADT_H
