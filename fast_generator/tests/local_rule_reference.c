/*
 * A separate, symbol-at-a-time implementation of the local calculation of
 * Section 7.2, used only to test the table-driven generator.
 *
 * Each Producer holds the bounded record of Section 7.2: w, z, R, D, A, the last four
 * upper-column bits before m, and the queue Q. next_symbol() performs one
 * complete queen-placement step (Section 4.5). When the step needs a symbol
 * beyond the end of Q, it asks a child producer, a second copy of the same
 * calculation started at the seed, for its next symbol (Section 7.1). No
 * table, history graph, or occupancy array is used.
 *
 * The tests use this file in two ways:
 *   - tests/check_local_steps.c and tests/check_table_paths.c include it and
 *     replay every finite case written by tools/build_tables.py through
 *     next_symbol(); they replace malloc so that a request for input is
 *     detected instead of creating a child;
 *   - built on its own as build/local_rule_reference, it is one of the
 *     programs whose coordinates tests/check_coordinates.py compares.
 *
 * Build: cc -O3 -std=c11 -DNDEBUG -Wall -Wextra -Wpedantic local_rule_reference.c
 * Run:   ./a.out --count 1000000
 *        ./a.out --count 100 --emit
 * Counts include the origin. --emit prints zero-based "column row" pairs and
 * sends the JSON summary to stderr; otherwise only the summary is printed.
 * The checksum is the one of queens_fast: starting from
 * 14695981039346656037, replace h by (h xor row) * 1099511628211 modulo 2^64
 * for each row.
 *
 * state_bytes counts the producer records; algorithm_bytes adds the outer
 * generator's three coordinate counters. fixed_seed_bytes is the seed.
 * seconds is the C clock() time of initialization and generation.
 */
#include <assert.h>
#include <errno.h>
#include <inttypes.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

enum { START = 30, PAST_BITS = 4, QUEUE_MAX = 11 };

typedef struct Producer Producer;
struct Producer {
    Producer *child;
    uint32_t queue;       /* Oldest two-bit symbol at the low end. */
    uint16_t masks;       /* R in bits 0..4, D in 5..9, A in 10..13. */
    uint8_t past_length;  /* Last four u bits, then four-bit queue length. */
    uint8_t positions;    /* w+4 in low four bits, z+4 in high four bits. */
};

typedef struct {
    Producer producer;
    uint64_t column;
    uint64_t m;
    uint64_t upper_count;
} QueenGenerator;

static uint8_t seed_queens[START];
static Producer seed;
static uint8_t seed_m, seed_upper;

static void fail(const char *message)
{
    fprintf(stderr, "local_rule_reference: %s\n", message);
    exit(EXIT_FAILURE);
}

static int maximum(int a, int b) { return a > b ? a : b; }
static int minimum(int a, int b) { return a < b ? a : b; }

/* C truncates negative division; the source algorithm uses floor division. */
static int floor_half(int x) { return x >= 0 ? x / 2 : -((1 - x) / 2); }

static int row_is_used(int y, int count)
{
    int i;
    for (i = 0; i < count; ++i)
        if (seed_queens[i] == y) return 1;
    return 0;
}

/* Compute the fixed seed from the greedy rule itself, independently of the
 * bounded-state update.  All storage and all work here are constant. */
static void make_seed(void)
{
    uint8_t symbols[START];
    unsigned rows = 0, differences = 0, sums = 0, past = 0;
    uint32_t queue = 0;
    int n, y, i, used, m, d, kappa = 0, w, z;
    for (n = 0; n < START; ++n) {
        for (y = 0; ; ++y) {
            used = 0;
            for (i = 0; i < n; ++i)
                if (seed_queens[i] == y || seed_queens[i] - i == y - n ||
                    seed_queens[i] + i == y + n) {
                    used = 1;
                    break;
                }
            if (!used) break;
        }
        assert(y <= UINT8_MAX);
        seed_queens[n] = (uint8_t)y;
    }
    seed_upper = 0;
    for (n = 0; n < START; ++n) {
        int b = 0, u = seed_queens[n] > n;
        for (i = 0; i < START; ++i)
            if (seed_queens[i] > i && seed_queens[i] == n) b = 1;
        symbols[n] = (uint8_t)(2 * u + b);
        seed_upper = (uint8_t)(seed_upper + u);
    }
    for (m = 0; row_is_used(m, START); ++m) {}
    for (d = 1; ; ++d) {
        used = 0;
        for (i = 0; i < START; ++i)
            if (i - seed_queens[i] == d) used = 1;
        if (!used) break;
    }
    for (i = 0; i < m; ++i) kappa += seed_queens[i] > i;
    for (i = 0; i < START; ++i) {
        y = seed_queens[i];
        if (y < i) {
            if (y >= m) rows |= 1u << (y - m);
            if (i - y >= d) differences |= 1u << (i - y - d);
            if (i + y >= START + m) sums |= 1u << (i + y - START - m);
        }
    }
    for (i = 0; i < PAST_BITS; ++i)
        past |= (unsigned)(symbols[m - 1 - i] >> 1) << i;
    for (i = m; i < START; ++i)
        queue |= (uint32_t)symbols[i] << (2 * (i - m));
    w = START - m - d;
    z = START - m - kappa;
    assert(START - m >= 1 && START - m <= QUEUE_MAX);
    assert(rows < 32 && differences < 32 && sums < 16);
    seed.child = NULL;
    seed.queue = queue;
    seed.masks = (uint16_t)(rows | differences << 5 | sums << 10);
    seed.past_length = (uint8_t)(past | (unsigned)(START - m) << 4);
    seed.positions = (uint8_t)((w + 4) | (z + 4) << 4);
    seed_m = (uint8_t)m;
}

/* Result bits: symbol in 0..1, row advance in 2..4, chosen r in 5..7.
 * The chosen-r field is unused when the symbol's upper-column bit is set. */
static unsigned next_symbol(Producer *p);

static void ensure(Producer *p, uint32_t *queue, unsigned *length, int needed)
{
    if ((int)*length >= needed) return;
    assert(needed <= 7);
    if (p->child == NULL) {
        p->child = (Producer *)malloc(sizeof(*p->child));
        if (p->child == NULL) fail("cannot allocate a child producer");
        *p->child = seed;
    }
    do {
        unsigned symbol = next_symbol(p->child) & 3u;
        assert(*length < QUEUE_MAX);
        *queue |= (uint32_t)symbol << (2 * *length);
        ++*length;
    } while ((int)*length < needed);
}

static unsigned next_symbol(Producer *p)
{
    int w = (p->positions & 15) - 4;
    int z = (p->positions >> 4) - 4;
    unsigned rows = p->masks & 31u;
    unsigned differences = (p->masks >> 5) & 31u;
    unsigned sums = p->masks >> 10;
    unsigned past = p->past_length & 15u;
    unsigned length = p->past_length >> 4;
    uint32_t queue = p->queue;
    unsigned blocked = rows | sums, row_bit = 0;
    unsigned diagonal_advance = 0, row_advance = 0, upper_advance = 0;
    int count = 0, distance, h, r, chosen = -1, limit;
    unsigned symbol, bits;

    ensure(p, &queue, &length, maximum(1, maximum(z, w + 1)));
    bits = past;
    for (distance = 1; distance <= PAST_BITS; ++distance) {
        if (bits & 1u) {
            row_bit |= (unsigned)(-distance - count == z);
            r = -2 * distance - count - z;
            if (r >= 0 && r <= w) blocked |= 1u << r;
            ++count;
        }
        bits >>= 1;
    }
    count = 0;
    limit = minimum((int)length, maximum(0, maximum(z, floor_half(z + w) + 1)));
    for (h = 0; h < limit; ++h) {
        if ((queue >> (2 * h + 1)) & 1u) {
            ++count;
            row_bit |= (unsigned)(h + count == z);
            r = 2 * h + count - z;
            if (r >= 0 && r <= w) blocked |= 1u << r;
        }
    }
    for (r = 0; r <= w; ++r)
        if (!((blocked >> r) & 1u) &&
            !((differences >> (w - r)) & 1u) &&
            !((queue >> (2 * r)) & 1u)) {
            chosen = r;
            break;
        }
    symbol = 2u * (unsigned)(chosen < 0) + row_bit;
    if (chosen >= 0) {
        rows |= 1u << chosen;
        differences |= 1u << (w - chosen);
        sums |= 1u << chosen;
    }
    while ((differences >> diagonal_advance) & 1u) ++diagonal_advance;
    for (;;) {
        ensure(p, &queue, &length, (int)row_advance + 1);
        if (!((rows >> row_advance) & 1u) &&
            !((queue >> (2 * row_advance)) & 1u)) break;
        ++row_advance;
    }
    for (h = 0; h < (int)row_advance; ++h) {
        unsigned upper = (queue >> 1) & 1u;
        upper_advance += upper;
        past = ((past << 1) | upper) & 15u;
        queue >>= 2;
    }
    w += 1 - (int)row_advance - (int)diagonal_advance;
    z += 1 - (int)row_advance - (int)upper_advance;
    rows >>= row_advance;
    differences >>= diagonal_advance;
    sums >>= row_advance + 1;
    length -= row_advance;
    assert(w >= -4 && w <= 4 && z >= -4 && z <= 5);
    assert(z - w >= -4 && z - w <= 3);
    assert(rows < 32 && !(rows & 1u));
    assert(differences < 32 && !(differences & 1u) && sums < 16);
    assert(length >= 1 && length <= QUEUE_MAX && row_advance <= 6);
    assert((queue >> (2 * length)) == 0 && !(queue & 1u));
    p->queue = queue;
    p->masks = (uint16_t)(rows | differences << 5 | sums << 10);
    p->past_length = (uint8_t)(past | length << 4);
    p->positions = (uint8_t)((w + 4) | (z + 4) << 4);
    return symbol | row_advance << 2 | (unsigned)(chosen < 0 ? 0 : chosen) << 5;
}

static uint64_t next_queen(QueenGenerator *g)
{
    uint64_t y, n = g->column++;
    if (n < START) return seed_queens[n];
    {
        unsigned result = next_symbol(&g->producer);
        if (result & 2u) y = n + ++g->upper_count;
        else y = g->m + (result >> 5);
        g->m += (result >> 2) & 7u;
    }
    return y;
}

static uint64_t parse_count(const char *text)
{
    char *end;
    unsigned long long value;
    if (*text == '\0' || *text == '-' || *text == '+') fail("invalid count");
    errno = 0;
    value = strtoull(text, &end, 10);
    if (errno == ERANGE || *end != '\0' || value > UINT64_MAX / 2)
        fail("count must be an integer between 0 and UINT64_MAX/2");
    return (uint64_t)value;
}

int main(int argc, char **argv)
{
    QueenGenerator generator;
    Producer *p;
    uint64_t count = 0, y = 0, hash = UINT64_C(14695981039346656037), n;
    size_t levels = 0, state_bytes, algorithm_bytes;
    int emit = 0, have_count = 0, i;
    clock_t started, finished;
    FILE *summary;
    for (i = 1; i < argc; ++i) {
        if (!strcmp(argv[i], "--emit")) emit = 1;
        else if (!strcmp(argv[i], "--count") && i + 1 < argc) {
            if (have_count) fail("count supplied more than once");
            count = parse_count(argv[++i]);
            have_count = 1;
        } else if (!strcmp(argv[i], "--help")) {
            printf("Usage: %s --count N [--emit]\n", argv[0]);
            return EXIT_SUCCESS;
        } else fail("usage: local_rule_reference --count N [--emit]");
    }
    if (!have_count) fail("--count is required");
    started = clock();
    make_seed();
    generator.producer = seed;
    generator.column = 0;
    generator.m = seed_m;
    generator.upper_count = seed_upper;
    if (emit) {
        for (n = 0; n < count; ++n) {
            y = next_queen(&generator);
            hash = (hash ^ y) * UINT64_C(1099511628211);
            printf("%" PRIu64 " %" PRIu64 "\n", n, y);
        }
    } else {
        for (n = 0; n < count; ++n) {
            y = next_queen(&generator);
            hash = (hash ^ y) * UINT64_C(1099511628211);
        }
    }
    finished = clock();
    for (p = &generator.producer; p != NULL; p = p->child) ++levels;
    state_bytes = levels * sizeof(Producer);
    algorithm_bytes = sizeof(QueenGenerator) + (levels - 1) * sizeof(Producer);
    summary = emit ? stderr : stdout;
    fprintf(summary, "{\"algorithm\":\"recursive-stream\",\"count\":%" PRIu64
            ",\"last_column\":", count);
    if (count) fprintf(summary, "%" PRIu64 ",\"last_queen\":%" PRIu64, count - 1, y);
    else fprintf(summary, "null,\"last_queen\":null");
    fprintf(summary, ",\"hash\":\"%016" PRIx64 "\",\"levels\":%zu"
            ",\"producer_bytes\":%zu,\"state_bytes\":%zu,\"algorithm_bytes\":%zu"
            ",\"fixed_seed_bytes\":%zu,\"seconds\":%.6f}\n",
            hash, levels, sizeof(Producer), state_bytes, algorithm_bytes,
            sizeof(seed_queens) + sizeof(seed) + sizeof(seed_m) + sizeof(seed_upper),
            (double)(finished - started) / CLOCKS_PER_SEC);
    p = generator.producer.child;
    while (p != NULL) {
        Producer *child = p->child;
        free(p);
        p = child;
    }
    return EXIT_SUCCESS;
}
