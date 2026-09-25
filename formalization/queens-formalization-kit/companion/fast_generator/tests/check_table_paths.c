/* Replay every four-input path of generated/block_cases.txt through the
 * separate implementation next_symbol() of tests/local_rule_reference.c, and
 * compare it with the compiled table of generated/tables.h.
 *
 * Each line describes one path of four input transitions on the graph of
 * 300 paused records (Section 7.3): its table index, the base offsets of its
 * starting and ending classes, the starting record with the four input
 * symbols already appended to Q, the expected outputs, and the ending
 * record. For each path this program
 *   1. calls next_symbol() once per expected output and compares, checking
 *      that no further input is requested (malloc is replaced by a function
 *      that jumps back here, as in check_local_steps.c);
 *   2. checks that one more call does request input, and that the record
 *      reached is the expected paused record;
 *   3. checks the table entry: its row, successor, length, symbols, and its
 *      coordinate data, recomputed from the outputs as in the coordinate formula of Section 7.3.
 *
 * Usage: build/check_table_paths generated/block_cases.txt
 */
#include <setjmp.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
static jmp_buf input_request;
static void *trap_input_request(size_t bytes) { (void)bytes; longjmp(input_request, 1); }
#define malloc trap_input_request
#define main local_rule_reference_main
#include "local_rule_reference.c"
#undef malloc
#undef main
#include "../generated/tables.h"
static void require(int value, const char *message, unsigned line)
{
    if (!value) { fprintf(stderr, "path %u: %s\n", line, message); exit(1); }
}
int main(int argc, char **argv)
{
    if (argc != 2) return 2;
    FILE *f = fopen(argv[1], "r");
    if (!f) { perror(argv[1]); return 1; }
    unsigned cases = 0, local_steps = 0;
    make_seed();
    for (;;) {
        unsigned index, owner, target, q, masks, past, positions, length;
        int n = fscanf(f, "%u %u %u %u %u %u %u %u",
                       &index, &owner, &target, &q, &masks, &past, &positions, &length);
        if (n == EOF) break;
        ++cases;
        require(n == 8 && length >= 3 && length <= 12, "malformed case", cases);
        unsigned values[12], nq, nm, np, nx;
        for (unsigned k = 0; k < length; ++k)
            require(fscanf(f, "%u", values + k) == 1, "malformed output", cases);
        require(fscanf(f, "%u %u %u %u", &nq, &nm, &np, &nx) == 4, "malformed successor", cases);

        /* 1-2. The local calculation, one queen at a time. */
        Producer p = {NULL, (uint32_t)q, (uint16_t)masks, (uint8_t)past, (uint8_t)positions};
        for (volatile unsigned k = 0; k < length; ++k) {
            require(setjmp(input_request) == 0, "unexpected request for input", cases);
            require(next_symbol(&p) == values[k], "reference output differs", cases);
            ++local_steps;
        }
        require(p.queue == nq && p.masks == nm && p.past_length == np && p.positions == nx,
                "reference successor differs", cases);
        if (setjmp(input_request) == 0) {
            (void)next_symbol(&p);
            require(0, "the reference produced an output without further input", cases);
        }

        /* 3. The compiled table entry. */
        require(index < QF_SLOT_COUNT && qf_owners[index] == owner, "table row differs", cases);
        uint64_t entry = qf_table[index];
        require((entry & QF_STATE_MASK) == target, "table successor differs", cases);
        require(((entry >> QF_LENGTH_SHIFT) & QF_LENGTH_MASK) == length, "table length differs", cases);
        uint64_t symbols = (entry >> QF_SYMBOL_SHIFT) & QF_SYMBOL_MASK;
        const uint8_t *data = qf_packets + (entry >> QF_PACKET_SHIFT);
        require(data[0] == length, "coordinate data length differs", cases);
        unsigned mu_total = 0, u_total = 0;
        for (volatile unsigned k = 0; k < length; ++k) {
            unsigned v = values[k];
            require(((symbols >> (2 * k)) & 3u) == (v & 3u), "table symbol differs", cases);
            unsigned code;
            if (v & 2u) code = 128u + k + (++u_total);  /* upper: offset from n_0 + U_0 */
            else code = mu_total + (v >> 5);            /* lower: offset from m_0 */
            require(data[3 + k] == code, "coordinate code differs", cases);
            mu_total += (v >> 2) & 7u;
        }
        require(data[1] == mu_total && data[2] == u_total, "counter advances differ", cases);
    }
    fclose(f);
    require(cases == 3483, "number of paths differs", cases);
    printf("{\"verified\":true,\"four_input_paths\":%u,\"local_steps\":%u}\n",
           cases, local_steps);
    return 0;
}
