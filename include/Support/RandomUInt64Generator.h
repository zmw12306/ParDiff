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


#ifndef SUPPORT_RANDOMUINT64GENERATOR_H
#define SUPPORT_RANDOMUINT64GENERATOR_H

#include <cassert>
#include <cstdlib>
#include <random>

class RandomUInt64Generator {
private:
    static RandomUInt64Generator *RNG;

    std::random_device RD;
    std::mt19937_64 G;
    FILE *Log;

    unsigned Mode;
    enum RunMode {
        RM_Common,
        RM_Record,
        RM_Replay
    };

    RandomUInt64Generator();

    ~RandomUInt64Generator();

public:
    uint64_t operator()();

    static RandomUInt64Generator *get();
};

template<class T>
void randomShuffle(std::vector<T> &Vec, size_t Begin, size_t End) {
    if (End <= Begin) {
        return;
    }

    auto &RNG = *RandomUInt64Generator::get();
    assert(End >= Begin + 1);
    size_t N = End - Begin;
    for (size_t I = N - 1; I != 0; --I) {
        size_t Offset = RNG() % (I + 1);

        auto Temp = Vec[Begin + I];
        Vec[Begin + I] = Vec[Begin + Offset];
        Vec[Begin + Offset] = Temp;
    }
}

#endif //SUPPORT_RANDOMUINT64GENERATOR_H
