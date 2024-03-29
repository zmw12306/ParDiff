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

#ifndef SUPPORT_Z3MACRO_H
#define SUPPORT_Z3MACRO_H

#include "Support/Z3.h"

#define DEBUG_TYPE "Z3"

#define FREE_VAR "fv"
#define INDEX_VAR "ii"
#define PHI "phi"
#define ONEOF "oneof"
#define NAME "name"
#define LENGTH "len"
#define BYTE_ARRAY "B"
#define BYTE_ARRAY_RANGE "Brange"
#define BASE "O"
#define TRIP_COUNT "K"

#endif //SUPPORT_Z3MACRO_H
