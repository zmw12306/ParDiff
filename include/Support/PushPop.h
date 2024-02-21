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

#ifndef SUPPORT_PUSHPOP_H
#define SUPPORT_PUSHPOP_H

#include <cassert>
#include <ctype.h>
#include <set>
#include <vector>

template<typename T>
class PushPopVector {
private:
    std::vector<size_t> SizeStack;
    std::vector<T> ElementVector;

public:
    ~PushPopVector() = default;

    void add(T N) { ElementVector.push_back(N); }

    void push_back(T N) { add(N); }

    typename std::vector<T>::const_iterator begin() const {
        return ElementVector.begin();
    }

    typename std::vector<T>::const_iterator end() const {
        return ElementVector.end();
    }

    typename std::vector<T>::const_reverse_iterator rbegin() const {
        return ElementVector.rbegin();
    }

    typename std::vector<T>::const_reverse_iterator rend() const {
        return ElementVector.rend();
    }

    T &operator[](size_t Index) {
        assert(Index < size());
        return ElementVector[Index];
    }

    void push() { SizeStack.push_back(ElementVector.size()); }

    void pop(std::set<T> *GC = nullptr) {
        auto N = 1;
        size_t OrigSz = size();
        size_t TargetSz = OrigSz;
        while (N-- > 0) {
            assert(!SizeStack.empty());
            TargetSz = SizeStack.back();
            SizeStack.pop_back();
        }

        if (TargetSz != OrigSz) {
            assert(TargetSz < OrigSz);
            if (GC)
                for (auto K = TargetSz; K < OrigSz; ++K) {
                    GC->insert(ElementVector[K]);
                }
            ElementVector.erase(ElementVector.begin() + TargetSz, ElementVector.end());
        }
    }

    void reset() {
        std::vector<size_t>().swap(SizeStack);
        std::vector<T>().swap(ElementVector);
    }

    [[nodiscard]] size_t size() const { return ElementVector.size(); }

    [[nodiscard]] bool empty() const { return !size(); }

    const std::vector<T> &get() const { return ElementVector; }
};

template<typename T>
class PushPopSet {
protected:
    std::vector<size_t> SizeStack;
    std::vector<T> ElementVector;
    std::set<T> ElementSet;

public:
    ~PushPopSet() = default;

    bool contains(T Element) const {
        return ElementSet.count(Element);
    }

    typename std::set<T>::const_iterator find(T Element) const {
        return ElementSet.find(Element);
    }

    typename std::set<T>::const_iterator end() const {
        return ElementSet.end();
    }

    void add(T Element) {
        if (!contains(Element)) {
            ElementSet.insert(Element);
            ElementVector.push_back(Element);
        }
    }

    void push() {
        SizeStack.push_back(size());
    }

    void pop() {
        unsigned Num = 1;
        unsigned Idx = 0;
        while (Idx < Num) {
            size_t P = SizeStack.back();
            SizeStack.pop_back();
            while (size() > P) {
                auto Elmt = ElementVector.back();
                ElementVector.pop_back();
                ElementSet.erase(Elmt);
            }

            Idx++;
        }
    }

    void reset() {
        std::vector<size_t>().swap(SizeStack);
        std::vector<T>().swap(ElementVector);
        std::set<T>().swap(ElementSet);
    }

    size_t size() const {
        return ElementSet.size();
    }
};

#endif //SUPPORT_PUSHPOP_H
