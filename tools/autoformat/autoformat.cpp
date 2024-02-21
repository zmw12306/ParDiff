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

#include <assert.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

extern "C" {

static uint8_t *buf_base = 0;
static uint64_t buf_len = 0;
static bool start_logging = 0;
static uint64_t *call_stack = 0;
static uint64_t call_stack_len = 0;
static uint64_t call_stack_ptr = 0;

void autoformat_beginning(uint8_t *base, uint64_t len) {
    assert(start_logging == 0 && "we assume no recursive call on the entry func");
    buf_base = base;
    buf_len = len;
    start_logging = 1;

    call_stack = (uint64_t *) malloc(1000);
    call_stack_len = 1000;
    call_stack[0] = 0; // ensure at least one element
    call_stack_ptr = 1;
}

void autoformat_end() {
    assert(start_logging);
    assert(call_stack_ptr == 1);
    buf_base = 0;
    buf_len = 0;
    start_logging = 0;
    free(call_stack);
}

void autoformat_logging(uint8_t *ptr, uint64_t nbytes) {
    if (!start_logging) return;

    for (unsigned x = 0; x < nbytes; ++x) {
        uint64_t delta = ((uint64_t) ptr) + x - (uint64_t) buf_base;
        if (delta < buf_len) {
            // logging the offset and the call stack
            printf("[autoformat] %llu, ", delta);
            for (unsigned y = 0; y < call_stack_ptr; ++y) {
                printf("%llu, ", call_stack[y]);
            }
            printf("\n");
        }
    }
}

void autoformat_pushing(uint64_t func_id) {
    if (!start_logging) return;
    assert(call_stack);
    if (call_stack_ptr >= call_stack_len) {
        call_stack = (uint64_t *) realloc(call_stack, call_stack_len + 500);
        call_stack_len += 500;
    }
    call_stack[call_stack_ptr++] = func_id;
}

void autoformat_popping() {
    if (!start_logging) return;
    assert(call_stack_ptr > 0);
    call_stack_ptr--;
}

}