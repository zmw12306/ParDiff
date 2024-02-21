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


#ifndef SUPPORT_DEBUG_H
#define SUPPORT_DEBUG_H

#include <llvm/Support/raw_ostream.h>

#ifdef NDEBUG
#define pardiff_WARN(X)
#else
#define pardiff_WARN(X) llvm::outs() << "[WARN] " << X << "\n"
#endif

#define pardiff_INFO(X) llvm::outs() << "[INFO] " << X << "\n"

#endif //SUPPORT_DEBUG_H
