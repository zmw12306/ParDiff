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

#ifndef SUPPORT_TIMERECORDER_H
#define SUPPORT_TIMERECORDER_H

#include <chrono>

#include "Support/Debug.h"

class TimeRecorder {
private:
    std::chrono::steady_clock::time_point Begin;
    std::string Prefix;

public:
    /// the prefix should be in a style of "Doing sth"
    explicit TimeRecorder(const char *Prefix) : Begin(std::chrono::steady_clock::now()), Prefix(Prefix) {
        pardiff_INFO(this->Prefix + "...");
    }

    ~TimeRecorder() {
        std::chrono::steady_clock::time_point End = std::chrono::steady_clock::now();
        auto Mili = std::chrono::duration_cast<std::chrono::milliseconds>(End - Begin);
        if (Mili.count() > 1000) {
            pardiff_INFO(Prefix + " takes " + std::to_string(Mili.count() / 1000) + "s!");
        } else {
            pardiff_INFO(Prefix + " takes " + std::to_string(Mili.count()) + "ms!");
        }
    }
};

#endif //SUPPORT_TIMERECORDER_H
