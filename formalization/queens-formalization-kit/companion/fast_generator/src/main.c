/* Command-line interface: queens_fast --count N [--emit]
 *
 * Generates the rows q_0, ..., q_{N-1} and prints a one-line JSON summary:
 * the last column and row, the checksum of all N rows (see qf_hash in
 * queens_fast.h), the storage reported by qf_stats, and the processor time
 * of generation. With --emit, every "column row" pair is printed to stdout
 * and the summary goes to stderr.
 */
#include "queens_fast.h"
#include <errno.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static void usage(const char *name)
{
    fprintf(stderr, "Usage: %s --count N [--emit]\n", name);
}

/* Accept only a nonempty string of decimal digits not exceeding UINT64_MAX/2. */
static int parse_count(const char *text, uint64_t *value)
{
    if (!text[0]) return -1;
    for (const char *p = text; *p; ++p) if (*p < '0' || *p > '9') return -1;
    char *end;
    errno = 0;
    unsigned long long result = strtoull(text, &end, 10);
    if (errno || *end || result > UINT64_MAX / 2u) return -1;
    *value = (uint64_t)result;
    return 0;
}

int main(int argc, char **argv)
{
    uint64_t count = 0, y = 0, hash = UINT64_C(14695981039346656037);
    int have_count = 0, emit = 0;
    for (int i = 1; i < argc; ++i) {
        if (!strcmp(argv[i], "--count") && i + 1 < argc && !have_count) {
            if (parse_count(argv[++i], &count)) { usage(argv[0]); return 2; }
            have_count = 1;
        } else if (!strcmp(argv[i], "--emit") && !emit) {
            emit = 1;
        } else if (!strcmp(argv[i], "--help") && argc == 2) {
            usage(argv[0]); return 0;
        } else { usage(argv[0]); return 2; }
    }
    if (!have_count) { usage(argv[0]); return 2; }
    clock_t started = clock();
    QFGenerator *g = qf_create();
    if (!g) { perror("qf_create"); return 1; }
    if (emit) {
        for (uint64_t n = 0; n < count; ++n) {
            if (qf_next(g, &y)) { perror("qf_next"); qf_destroy(g); return 1; }
            hash = (hash ^ y) * UINT64_C(1099511628211);
            if (printf("%" PRIu64 " %" PRIu64 "\n", n, y) < 0) {
                perror("stdout"); qf_destroy(g); return 1;
            }
        }
    } else if (qf_hash(g, count, &hash, &y)) {
        perror("qf_hash"); qf_destroy(g); return 1;
    }
    clock_t finished = clock();
    QFStats stats = qf_stats(g);
    FILE *summary = emit ? stderr : stdout;
    /* "sparse-b4" names the table: sparse row placement, four input symbols
     * per lookup. algorithm_bytes is heap_bytes plus static_data_bytes. */
    fprintf(summary, "{\"algorithm\":\"queens-fast-sparse-b4\",\"count\":%" PRIu64
                    ",\"last_column\":", count);
    if (count) fprintf(summary, "%" PRIu64 ",\"last_queen\":%" PRIu64, count - 1u, y);
    else fputs("null,\"last_queen\":null", summary);
    fprintf(summary, ",\"hash\":\"%016" PRIx64 "\",\"levels\":%zu"
                    ",\"generator_bytes\":%zu,\"producer_record_bytes\":%zu"
                    ",\"symbol_buffer_bytes\":%zu,\"heap_bytes\":%zu"
                    ",\"static_data_bytes\":%zu,\"algorithm_bytes\":%zu"
                    ",\"outer_macro_steps\":%" PRIu64 ",\"inner_macro_steps\":%" PRIu64
                    ",\"refill_calls\":%" PRIu64 ",\"seconds\":%.9f}\n",
            hash, stats.levels, stats.generator_bytes, stats.producer_record_bytes,
            stats.symbol_buffer_bytes, stats.heap_bytes, stats.static_data_bytes,
            stats.heap_bytes + stats.static_data_bytes, stats.outer_macro_steps,
            stats.inner_macro_steps, stats.refill_calls,
            (double)(finished - started) / CLOCKS_PER_SEC);
    qf_destroy(g);
    if (fflush(stdout) || ferror(summary)) return 1;
    return 0;
}
