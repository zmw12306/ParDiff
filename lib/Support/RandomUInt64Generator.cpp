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

#include <llvm/ADT/Statistic.h>
#include <llvm/Support/CommandLine.h>

#include "Support/RandomUInt64Generator.h"

#define DEBUG_TYPE "RandomUInt64Generator"

using namespace llvm;

static cl::opt<std::string> Record("rng-record", cl::desc("record what integers are generated"),
                                   cl::init("/tmp/a.txt"), cl::ValueOptional);

static cl::opt<std::string> Replay("rng-replay", cl::desc("record what integers are generated"),
                                   cl::init("/tmp/a.txt"), cl::ValueOptional);

STATISTIC(Count, "Number of random number generated");

RandomUInt64Generator *RandomUInt64Generator::RNG = nullptr;

RandomUInt64Generator *RandomUInt64Generator::get() {
    if (RNG == nullptr) {
        RNG = new RandomUInt64Generator();
    }
    return RNG;
}

RandomUInt64Generator::RandomUInt64Generator() : G(RD()), Log(nullptr), Mode(RM_Common) {
    std::string File;
    if (Record.getNumOccurrences()) {
        Mode = RM_Record;
        File = Record.getValue().empty() ? "/tmp/a.txt" : "";
    } else if (Replay.getNumOccurrences()) {
        Mode = RM_Replay;
        File = Replay.getValue().empty() ? "/tmp/a.txt" : "";
    }

    if (Record.getNumOccurrences() && Replay.getNumOccurrences()) {
        errs() << "Cannot record/replay together, do record instead!\n";
    }

    if (Mode != RM_Common) {
        Log = fopen(File.c_str(), Mode == RM_Record ? "w" : "r");
        if (!Log) {
            errs() << "Fail to open " << File << "\n";
            Mode = RM_Common;
        }
    }
}

RandomUInt64Generator::~RandomUInt64Generator() {
    if (Log) {
        fclose(Log);
    }
}

uint64_t RandomUInt64Generator::operator()() {
    if (Mode == RM_Record) {
        uint64_t Ret = G();
        fwrite(&Ret, sizeof(uint64_t), 1, Log);
        fflush(Log);
        Count++;
        return Ret;
    } else if (Mode == RM_Replay) {
        uint64_t Ret;
        if (feof(Log)) {
            llvm_unreachable("nothing can read from log!");
        }
        fread(&Ret, sizeof(uint64_t), 1, Log);
        Count++;
        return Ret;
    } else {
        uint64_t Ret = G();
        return Ret;
    }
}
