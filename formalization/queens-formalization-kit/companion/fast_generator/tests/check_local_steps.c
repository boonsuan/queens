/* Replay every local case of generated/local_cases.txt through the separate
 * implementation next_symbol() of tests/local_rule_reference.c.
 *
 * tools/build_tables.py records every call of its local step: 574 complete
 * steps, each with its output and successor record, and 300 records at which
 * the step needs one more input symbol. Here each record is loaded into a
 * Producer and next_symbol() is called once. A request for input would make
 * next_symbol() allocate a child producer; malloc is replaced by a function
 * that jumps back here instead, so such a request is detected.
 *
 * Usage: build/check_local_steps generated/local_cases.txt
 * Each line is "0 record" (input needed) or "1 record output successor",
 * with records in the four-field format of pack_record() in the builder.
 */
#include <setjmp.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
static jmp_buf input_request;
static void *trap_input_request(size_t bytes)
{
    (void)bytes;
    longjmp(input_request, 1);
}
#define malloc trap_input_request
#define main local_rule_reference_main
#include "local_rule_reference.c"
#undef main
#undef malloc
static void require(int truth, const char *message, unsigned line)
{
    if (!truth) {
        fprintf(stderr, "case %u: %s\n", line, message);
        exit(1);
    }
}
int main(int argc, char **argv)
{
    if (argc != 2) return 2;
    FILE *input = fopen(argv[1], "r");
    if (!input) { perror(argv[1]); return 1; }
    make_seed();
    require(seed_m == 19 && seed_upper == 18, "seed counters", 0);
    unsigned cases = 0, complete = 0, requests = 0;
    for (;;) {
        unsigned mode, q, masks, past, positions;
        unsigned expected = 0, nq = 0, nm = 0, np = 0, nx = 0;
        int read = fscanf(input, "%u %u %u %u %u", &mode, &q, &masks, &past, &positions);
        if (read == EOF) break;
        require(read == 5 && mode <= 1, "malformed input", cases + 1);
        if (mode)
            require(fscanf(input, "%u %u %u %u %u", &expected, &nq, &nm, &np, &nx) == 5,
                    "malformed expected record", cases + 1);
        Producer p = {NULL, (uint32_t)q, (uint16_t)masks, (uint8_t)past, (uint8_t)positions};
        ++cases;
        if (setjmp(input_request) == 0) {
            unsigned value = next_symbol(&p);
            require(mode == 1, "the reference completed a step that the builder paused", cases);
            require(value == expected, "output differs", cases);
            require(!p.child && p.queue == nq && p.masks == nm &&
                    p.past_length == np && p.positions == nx, "successor differs", cases);
            ++complete;
        } else {
            require(mode == 0, "the reference requested input for a completed step", cases);
            ++requests;
        }
    }
    fclose(input);
    require(cases == 874 && complete == 574 && requests == 300, "number of cases differs", cases);
    printf("{\"verified\":true,\"cases\":%u,\"completed_steps\":%u,\"input_requests\":%u}\n",
           cases, complete, requests);
    return 0;
}
