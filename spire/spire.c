/* Spire: the greedy queens, 10^10 rows in 0.04 seconds.
 *
 * Spire computes the rows q_0, q_1, ... of the greedy queen sequence (the paper, Section 7)
 * and folds them into the polynomial checksum H = sum_n q_n P^(N-1-n) mod 2^64. Compiled with
 * ROWS=1 (spire-rows.c) it also writes every row to memory as a 64-bit number and sums them.
 * It uses logarithmic memory per thread, like the paper's generator, and all the threads of the
 * machine.
 *
 * THE IDEAS, in the order the code uses them (README.md tells the story at more length):
 *
 * 1. The paper's generator is a chain of copies of one calculation: copy 0 makes the rows,
 *    reading the queen word sigma; copy 1 makes that part of sigma, reading an earlier part;
 *    and so on down to the seed. Each copy is a transducer: in a state (one of 82 classes) it
 *    reads one byte (four symbols of sigma) and makes 3-12 symbols (or, for copy 0, 3-12 rows).
 *
 * 2. Any copy can be started anywhere. From the set of all 300 "paused records", the actual
 *    input symbols shrink it to the true record within 58 symbols (we read 128; proved in
 *    synchronization.py), and a record gives the copy's exact counters there. So each thread
 *    builds its own chain of copies for its own range of columns, and nothing is shared but
 *    the tables.
 *
 * 3. A stack of k consecutive copies is itself a transducer: its state is the k classes and
 *    the few (0-3) symbols pending between each two copies. One input byte of the stack drives
 *    the bottom copy one step and the copies above as far as they can go. We call such a stack
 *    a tower. Towers of height 2 ("pairs") make up the chain below the top; the top is a tower
 *    of height 8, whose input byte stands for about 190 rows.
 *
 * 4. Only a few transitions occur. Along sigma, a pair meets 8000 or so transitions and a
 *    tower of 8 about 23 500: sigma is so regular that taller towers barely add states. The
 *    tables hold exactly these (the "plan", which `make` computes into build/plan.h), densely
 *    packed, and every
 *    slot is tagged with the state it belongs to. A lookup whose tag differs (a transition
 *    never met) is computed from the base table instead, so the result is exact regardless.
 *
 * 5. A step's rows hash in closed form. The rows of a top step are m + offset or n + U +
 *    offset, where m is the least unused row and n + U the column plus the number of upper
 *    columns so far, both taken before the step. So the step adds m A + (n + U) B + C to the
 *    hash (after H <- H P^L, L its number of rows), with A, B, C fixed per slot. With
 *    F = (P - 1) H + m this is two multiplications a step, however many rows the step makes.
 *
 * 6. The machine sets the limits. The inner loops run four chains of lookups side by side to
 *    hide the cache's latency, keep every chain's state in a register, and do each step's work
 *    in a second loop that does not wait for the chains. On x86-64 with AVX2 and BMI2 they are
 *    in assembly (loops.S) and the tables sit at fixed addresses (layout.h); on any other
 *    64-bit processor, such as ARM64 (Apple Silicon, Graviton), they are in C (loops.c).
 *
 * The same code makes four programs (see "main" at the end):
 *     spire N [threads] [ranges]         the checksum of the first N rows
 *     spire-rows N [threads] [ranges]    the same, writing every row to memory (ROWS=1)
 *     spire-print A B [--binary] [threads]
 *                                        the rows q_A .. q_(B-1), to standard output (PRINT=1)
 *     spire-at n [n ...]                 each q_n alone, in time logarithmic in n (spire-at.c)
 * Numbers may be written 10000, 1e12 or 10^18, and B also as +k (for A + k).
 *
 * It builds under Linux, macOS and Windows (MSYS2), with GCC or clang and OpenMP.
 */
/* x86-64 with AVX2 and BMI2, under Linux or Windows, uses the assembly loops and fixed table
 * addresses; anything else (including macOS, which reserves the lowest 4 GB of every process,
 * or -DSPIRE_PORTABLE) the C loops and ordinary allocations. */
#if defined(__x86_64__) && defined(__AVX2__) && defined(__BMI2__) && !defined(__APPLE__) && !defined(SPIRE_PORTABLE)
#define SPIRE_X86 1
#else
#define SPIRE_X86 0
#endif
/* Rows are written with AVX-512 or AVX2 wherever available, and with NEON on ARM64. */
#if defined(__AVX512F__) && defined(__AVX512BW__) && defined(__AVX512VL__)
#define ROWS_AVX512 1
#else
#define ROWS_AVX512 0
#endif
#if defined(__AVX2__)
#define ROWS_AVX2 1
#include <immintrin.h>
#else
#define ROWS_AVX2 0
#if defined(__aarch64__)
#include <arm_neon.h>
#endif
#endif
#include <omp.h>
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#ifdef _WIN32
#include <windows.h>
#include <psapi.h>
#include <malloc.h>
#include <fcntl.h>
#include <io.h>
#else
#include <sys/mman.h>
#include <sys/resource.h>
#endif
#include "tables.h"   /* the base transducer (../fast_generator/generated/tables.h) */
#include "records.h"  /* the 300 paused records (build/records.h, from make_records.py) */
#include "layout.h"

#ifndef PRINT
#define PRINT 0             /* 1: write the rows out (spire-print) */
#endif
#ifndef AT
#define AT 0                /* 1: part of spire-at.c, which has its own main */
#endif
#ifndef ROWS
#define ROWS PRINT          /* 1: also write every row to memory (spire-rows, spire-print) */
#endif
#define TOP_HEIGHT 8        /* the copies in the top tower */
#define PAIR_HEIGHT 2       /* the copies in each tower of the chain below it */

/* The plan: which states and transitions the tables hold, and where (see "Building the
 * tables"). It is a pure function of the base table; `make` computes it into build/plan.h. */
typedef struct { uint64_t lo, hi; uint32_t x; } PlanEntry;  /* a state's key, and a slot or byte */
#if !defined(TRAIN) && __has_include("plan.h")
#include "plan.h"
#define HAVE_PLAN 1
#else
#define HAVE_PLAN 0
#endif

#define P UINT64_C(1099511628211)  /* the prime of the checksum (FNV's) */
static void die(const char *what, uint64_t x) { fprintf(stderr, "spire: %s %llu\n", what, (unsigned long long)x); exit(1); }
static uint64_t power(uint64_t b, uint64_t e) { uint64_t r = 1; while (e) { if (e & 1) r *= b; b *= b; e >>= 1; } return r; }
/* x / phi in 64.64 fixed point, for every 64-bit x: x times 1/phi = phi - 1 to 192 bits. The
 * integer part is exact (the error is below x 2^-192, and x/phi is never that close to an
 * integer: |x phi - k| > 1/(3x)); so is the fraction, to within 2^-63. */
static unsigned __int128 times_inv_phi(uint64_t x)
{
    typedef unsigned __int128 u128;
    const uint64_t f0 = UINT64_C(0x1082276bf3a27251), f1 = UINT64_C(0xf39cc0605cedc834), f2 = UINT64_C(0x9e3779b97f4a7c15);
    u128 t = ((u128)x * f1) + (((u128)x * f0) >> 64);
    return ((u128)x * f2) + (t >> 64);
}
static uint64_t div_phi(uint64_t x) { return (uint64_t)(times_inv_phi(x) >> 64); }  /* floor(x / phi) */
/* A count from the command line: 1000000, 1e12 or 10^18 (an exact integer below 2^64). */
static uint64_t parse_count(const char *s)
{
    char *end;
    int bad = *s < '0' || *s > '9';
    errno = 0;
    uint64_t a = strtoull(s, &end, 10), base = 0;
    if (*end == 'e' || *end == 'E') base = 10;
    else if (*end == '^') base = a, a = 1;
    if (base) {
        const char *x = end + 1;
        uint64_t e = strtoull(x, &end, 10);
        bad |= *x < '0' || *x > '9';
        for (uint64_t i = 0; i < e && !bad; ++i) {
            bad = base > 1 && a > UINT64_MAX / base;
            a *= base;
        }
    }
    if (bad || *end || errno == ERANGE) { fprintf(stderr, "spire: cannot read %s as a whole number below 2^64\n", s); exit(2); }
    return a;
}


/* ======================================================================================
 * The base transducer
 *
 * qf_table (from ../fast_generator) is the paper's generator: slot c + b is the step of class c
 * (a row offset in the table) reading byte b; its entry holds the next class, the number of
 * symbols made (3-12) and the symbols, and points to a packet with the step's row codes and
 * counter increments. We widen each entry to carry the increments too.
 * ====================================================================================== */
static uint64_t entry[QF_SLOT_COUNT];
#define NEXT(e)   ((unsigned)((e) & 4095u))                  /* the next class */
#define LEN(e)    ((unsigned)(((e) >> 12) & 15u))            /* symbols (= rows) made */
#define SYMS(e)   (((e) >> 16) & UINT64_C(0xFFFFFF))         /* the symbols, 2 bits each */
#define CODES(e)  (qf_packets + (((e) >> 40) & 0x3FFFu) + 3) /* row codes: upper bit | offset */
#define DM(e)     ((unsigned)(((e) >> 54) & 31u))            /* m advances by this */
#define DU(e)     ((unsigned)((e) >> 59))                    /* U advances by this */
static void widen_entries(void)
{
    for (unsigned i = 0; i < QF_SLOT_COUNT; ++i) {
        uint64_t e = qf_table[i];
        if (!((e >> QF_LENGTH_SHIFT) & QF_LENGTH_MASK)) { entry[i] = 0; continue; }
        const uint8_t *packet = qf_packets + (e >> QF_PACKET_SHIFT);
        entry[i] = (e & UINT64_C(0xFFFFFFFFFF)) | ((e >> QF_PACKET_SHIFT) << 40)
                 | ((uint64_t)packet[1] << 54) | ((uint64_t)packet[2] << 59);
    }
}
/* Whether class c can read byte b at all (slot c + b belongs to c). */
static inline int accepts(unsigned c, unsigned b) { return c + b < QF_SLOT_COUNT && qf_owners[c + b] == c; }
/* The upper columns among packed symbols: the high bit of each 2-bit symbol. */
static inline unsigned uppers(uint64_t syms) { return (unsigned)__builtin_popcountll(syms & UINT64_C(0xAAAAAAAAAAAAAAAA)); }
static inline unsigned symbol(uint64_t syms, unsigned j) { return (unsigned)(syms >> (2 * j)) & 3; }


/* ======================================================================================
 * Towers, simulated exactly (slowly)
 *
 * A tower of height h: copy 0 on top, copy h-1 at the bottom reading the input bytes. q[i]
 * holds the symbols copy i+1 has made and copy i has not yet read. A step reads one input
 * byte, then lets copies h-2, ..., 1, 0 read everything they can; afterwards fewer than four
 * symbols are pending anywhere, so the tower's state is its classes and those short queues.
 *
 * The key of a state packs, for each copy, its class number (7 bits: there are 82 classes)
 * and, for each queue, a code for its 0-3 symbols (7 bits: 1 + 4 + 16 + 64 possibilities).
 * ====================================================================================== */
#define MAX_HEIGHT 8
#define QUEUE 32768            /* a queue can hold thousands of symbols during a step */
#define MAX_BLOCKS 4096        /* copy 0's steps in one tower step (at most 3^7) */
typedef unsigned __int128 Key;
typedef struct {
    unsigned height, cls[MAX_HEIGHT], n[MAX_HEIGHT], h[MAX_HEIGHT];  /* q[i][h[i] .. n[i]) pending */
    uint8_t q[MAX_HEIGHT][QUEUE];
} Tower;
/* Copy 0's steps in a tower step: the base slots it used, each giving 3-12 rows (or symbols). */
typedef struct { unsigned n; uint16_t slot[MAX_BLOCKS]; } Blocks;
static __thread Tower scratch_tower;  /* too large for the stack */
static __thread Blocks scratch_blocks;

static uint16_t class_base[128];            /* class number -> class (row offset in qf_table) */
static uint8_t class_number[QF_SLOT_COUNT];
static void number_classes(void)
{
    static uint8_t seen[QF_SLOT_COUNT];
    unsigned n = 0;
    for (unsigned i = 0; i < QF_SLOT_COUNT; ++i) {
        unsigned c = qf_owners[i];
        if (c == 65535 || seen[c]) continue;
        seen[c] = 1;
        class_base[n] = (uint16_t)c; class_number[c] = (uint8_t)n++;
    }
}
static Key tower_key(const Tower *w)
{
    Key k = 0;
    for (unsigned i = 0; i < w->height; ++i) k |= (Key)class_number[w->cls[i]] << (7 * i);
    for (unsigned i = 0; i + 1 < w->height; ++i) {
        unsigned n = w->n[i] - w->h[i], v = 0;
        if (n > 3) die("symbols left pending in a tower:", n);
        for (unsigned j = 0; j < n; ++j) v |= (unsigned)w->q[i][w->h[i] + j] << (2 * j);
        k |= (Key)(((1u << (2 * n)) - 1) / 3 + v) << (7 * (w->height + i));
    }
    return k;
}
static void tower_load(Tower *w, unsigned height, Key k)
{
    w->height = height;
    for (unsigned i = 0; i < height; ++i) { w->cls[i] = class_base[(unsigned)(k >> (7 * i)) & 127]; w->h[i] = 0; w->n[i] = 0; }
    for (unsigned i = 0; i + 1 < height; ++i) {
        unsigned code = (unsigned)(k >> (7 * (height + i))) & 127;
        unsigned n = code >= 21 ? 3 : code >= 5 ? 2 : code >= 1 ? 1 : 0, v = code - ((1u << (2 * n)) - 1) / 3;
        w->n[i] = n;
        for (unsigned j = 0; j < n; ++j) w->q[i][j] = (uint8_t)((v >> (2 * j)) & 3);
    }
}
static inline void queue_put(Tower *w, unsigned i, uint64_t e)
{
    if (w->n[i] + 16 > QUEUE) die("tower queue overflow at copy", i);
    for (unsigned j = 0; j < LEN(e); ++j) w->q[i][w->n[i]++] = (uint8_t)symbol(SYMS(e), j);
}
static inline unsigned queue_take(Tower *w, unsigned i)  /* four symbols as a byte */
{
    const uint8_t *s = w->q[i] + w->h[i];
    w->h[i] += 4;
    return s[0] | s[1] << 2 | s[2] << 4 | s[3] << 6;
}
static inline void queue_compact(Tower *w, unsigned i)
{
    unsigned r = w->n[i] - w->h[i];
    memmove(w->q[i], w->q[i] + w->h[i], r); w->n[i] = r; w->h[i] = 0;
}
/* Let copies h-2, ..., 1 and then 0 read all they can; copy 0's steps go to `out`.
 * 0 if some copy meets a byte its class cannot read (then the input was not sigma). */
static int tower_settle(Tower *w, Blocks *out)
{
    for (int i = (int)w->height - 2; i >= 0; --i) {
        while (w->n[i] - w->h[i] >= 4) {
            unsigned b = queue_take(w, (unsigned)i);
            if (!accepts(w->cls[i], b)) return 0;
            uint64_t e = entry[w->cls[i] + b];
            if (i > 0) queue_put(w, (unsigned)i - 1, e);
            else { if (out->n == MAX_BLOCKS) die("tower step too long", out->n); out->slot[out->n++] = (uint16_t)(w->cls[0] + b); }
            w->cls[i] = NEXT(e);
        }
        queue_compact(w, (unsigned)i);
    }
    return 1;
}
/* One input byte of a tower: its next key and copy 0's steps. 0 if the byte is rejected. */
static int tower_step(unsigned height, Key key, unsigned b, Key *next, Blocks *out)
{
    Tower *w = &scratch_tower;
    tower_load(w, height, key);
    unsigned bottom = height - 1;
    if (!accepts(w->cls[bottom], b)) return 0;
    uint64_t e = entry[w->cls[bottom] + b];
    queue_put(w, bottom - 1, e);
    w->cls[bottom] = NEXT(e);
    out->n = 0;
    if (!tower_settle(w, out)) return 0;
    *next = tower_key(w);
    return 1;
}
/* The tower at the very start: every copy has made its first 18 symbols (sigma_30..47, the
 * seed's), and the copies above have read them as far as they can. */
static Key tower_seed(unsigned height, Blocks *out)
{
    Tower *w = &scratch_tower;
    w->height = height;
    for (unsigned i = 0; i < height; ++i) { w->cls[i] = QF_INITIAL_STATE; w->n[i] = w->h[i] = 0; }
    for (unsigned i = 0; i + 1 < height; ++i)
        for (unsigned j = 0; j < QF_INITIAL_LENGTH; ++j) w->q[i][w->n[i]++] = (uint8_t)symbol(QF_INITIAL_SYMBOLS, j);
    out->n = 0;
    if (!tower_settle(w, out)) die("the seed tower is rejected", 0);
    return tower_key(w);
}


/* ======================================================================================
 * What a step does
 *
 * A pair's step makes the symbols of its copy 0's steps (at most 28 of them), packed with
 * their number: symbols << 8 | 2 * number.
 *
 * The top's step makes L rows. Row r is m + offset_r or (n + U) + offset_r, with m and n + U
 * taken before the step (the offsets include the step's own increments of m and U before row
 * r). So the step adds m A + (n + U) B + C to the checksum after H <- H P^L, where
 *     B = sum over the upper rows of P^(L-1-r),  A = S(L) - B,  C = sum of offset_r P^(L-1-r),
 * S(L) = 1 + P + ... + P^(L-1). Since (P - 1) S(L) = P^L - 1, the value F = (P - 1) H + m obeys
 *     F <- F P^L + D (P - 1) B + (P - 1) C + dm,    D = (n + U) - m,
 * and m needs no multiplication. (P - 1 is even, so F determines H modulo 2^63: the program
 * reports H mod 2^63.) A slot of the top table holds {L | dm << 24, (P-1) B, (P-1) C + dm,
 * dnu - dm}, dnu being the advance of n + U.
 * ====================================================================================== */
typedef struct { uint64_t lm, b, c, dd; } TopStep;
static uint64_t pair_symbols(const Blocks *bl)
{
    uint64_t syms = 0;
    unsigned n = 0;
    for (unsigned j = 0; j < bl->n; ++j) {
        uint64_t e = entry[bl->slot[j]];
        if (n + LEN(e) > 28) die("a pair step makes too many symbols:", n + LEN(e));
        syms |= SYMS(e) << (2 * n); n += LEN(e);
    }
    return syms << 8 | 2 * n;
}
static TopStep top_step(const Blocks *bl)
{
    uint64_t L = 0, dm = 0, dnu = 0, B = 0, C = 0;  /* B and C by Horner's rule, row by row */
    for (unsigned j = 0; j < bl->n; ++j) {
        uint64_t e = entry[bl->slot[j]];
        const uint8_t *codes = CODES(e);
        for (unsigned i = 0; i < LEN(e); ++i) {
            unsigned upper = codes[i] >> 7;
            B = B * P + upper;
            C = C * P + (upper ? dnu : dm) + (codes[i] & 127);
        }
        L += LEN(e); dm += DM(e); dnu += LEN(e) + DU(e);
    }
    if (L >= 65536) die("a top step makes too many rows:", L);
    TopStep s = {dm << 24 | L, (P - 1) * B, (P - 1) * C + dm, dnu - dm};
    return s;
}


/* ======================================================================================
 * The tables
 *
 * A machine (the pairs, or the top tower) has a state map (key <-> state number <-> row) and
 * its tables at fixed addresses (layout.h). A state's row is its first slot; the slot for
 * byte b is row + code(b), and holds:
 *     chain:  tag | next << 16     the tag is the row the slot belongs to; next the next row
 *     pairs:  the symbols made     top:  the TopStep (and, for rows, the step's block list).
 * Rows are 16-bit numbers. States met only at run time (by the slow path) get private empty
 * rows after the table, so their lookups always miss.
 * ====================================================================================== */
#define MAX_STATES 16384
#define MAP_SIZE 65536
typedef struct {
    unsigned height;
    uint32_t *chain;                 /* PAIR_CHAINS or TOP_CHAINS */
    Key key[MAX_STATES];             /* state -> key */
    uint32_t row[MAX_STATES];        /* state -> row (UINT32_MAX until known) */
    Key map_key[MAP_SIZE];           /* key -> state, open addressing */
    uint32_t map_state[MAP_SIZE];
    uint8_t map_used[MAP_SIZE];
    uint32_t nstates, nslots;        /* the table's slots are 0 .. nslots-1 */
    uint32_t *state_at;              /* row -> state, for rows in the table */
} Machine;
static Machine pairs, top;
static omp_lock_t slow_lock;         /* the state maps are shared; only the slow path adds */
static uint64_t slow_steps;
static uint16_t *top_block_lists;    /* rows only: each top slot's copy-0 steps */
typedef struct { int8_t code[12]; uint8_t len, dm, dnu, pad; } BaseRows;  /* rows only */
static BaseRows base_rows[QF_SLOT_COUNT] __attribute__((aligned(64)));
#if defined(__aarch64__)
/* Rows only, on ARM64: the codes widened for NEON, row = (upper ? nu : m) + offset, so that two
 * rows take a select and an add. */
typedef struct { int64_t offset[12]; uint64_t upper[12]; } WideRows;
static WideRows wide_rows[QF_SLOT_COUNT] __attribute__((aligned(64)));
#endif
/* The tables: at the fixed addresses of layout.h on x86-64 (so that the assembly can name
 * them), otherwise wherever they were allocated. */
static uint32_t *byte_code_table, *pair_chain_table, *top_chain_table;
static uint64_t *power_table, *pair_symbol_table, *top_block_ref_table;
static TopStep *top_step_table;
#if SPIRE_X86
#define BYTE_CODES ((uint32_t *)BYTE_CODE)
#define POWERS ((uint64_t *)POWER_OF_P)
#define PAIR_CHAINS ((uint32_t *)PAIR_CHAIN)
#define TOP_CHAINS ((uint32_t *)TOP_CHAIN)
#define PAIR_SYMBOLS ((uint64_t *)PAIR_SYMS)
#define TOP_STEPS ((TopStep *)TOP_STEP)
#define TOP_BLOCK_REFS ((uint64_t *)TOP_BLOCKS)
#else
#define BYTE_CODES byte_code_table
#define POWERS power_table
#define PAIR_CHAINS pair_chain_table
#define TOP_CHAINS top_chain_table
#define PAIR_SYMBOLS pair_symbol_table
#define TOP_STEPS top_step_table
#define TOP_BLOCK_REFS top_block_ref_table
#endif

static uint32_t state_of_key(Machine *M, Key k)
{
    uint64_t f = (uint64_t)k ^ (uint64_t)(k >> 64) * UINT64_C(0xC2B2AE3D27D4EB4F);
    uint32_t h = (uint32_t)((f * UINT64_C(0x9E3779B97F4A7C15)) >> 48);
    while (M->map_used[h]) { if (M->map_key[h] == k) return M->map_state[h]; h = (h + 1) & (MAP_SIZE - 1); }
    if (M->nstates == MAX_STATES) die("too many states in a tower of height", M->height);
    M->map_used[h] = 1; M->map_key[h] = k; M->map_state[h] = M->nstates;
    M->key[M->nstates] = k; M->row[M->nstates] = UINT32_MAX;
    return M->nstates++;
}
static uint32_t row_of_state(Machine *M, uint32_t s)
{
    if (M->row[s] == UINT32_MAX) M->row[s] = M->nslots + s;  /* a private empty row */
    return M->row[s];
}
static uint32_t state_of_row(const Machine *M, uint64_t row) { return row < M->nslots ? M->state_at[row] : (uint32_t)(row - M->nslots); }
/* Zeroed memory for a table: at a fixed address on x86-64 (the operating system places it
 * there if the range is free), anywhere otherwise. */
static void *reserve_at(uint64_t where, size_t bytes)
{
#if SPIRE_X86
#ifdef _WIN32
    void *a = VirtualAlloc((void *)(uintptr_t)where, bytes, MEM_RESERVE | MEM_COMMIT, PAGE_READWRITE);
#else
    void *a = mmap((void *)(uintptr_t)where, bytes, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
#endif
    if (a != (void *)(uintptr_t)where) die("cannot reserve the table at address", where);
    return a;
#else
    (void)where;
    void *p = calloc(1, bytes);
    if (!p) die("out of memory for a table of bytes:", bytes);
    return p;
#endif
}
/* 64-byte aligned buffers. */
static void *aligned_alloc64(size_t bytes)
{
    void *p;
#ifdef _WIN32
    p = _aligned_malloc(bytes, 64);
#else
    if (posix_memalign(&p, 64, bytes)) p = NULL;
#endif
    if (!p) die("out of memory for a buffer of bytes:", bytes);
    return p;
}
static void aligned_free64(void *p)
{
#ifdef _WIN32
    _aligned_free(p);
#else
    free(p);
#endif
}
/* Seconds, from a monotonic clock with a resolution of a microsecond or better. */
static double now(void)
{
#ifdef _WIN32
    LARGE_INTEGER f, c;
    QueryPerformanceFrequency(&f); QueryPerformanceCounter(&c);
    return (double)c.QuadPart / (double)f.QuadPart;
#else
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (double)t.tv_sec + 1e-9 * (double)t.tv_nsec;
#endif
}
/* The most physical memory the process has held, in bytes. */
static double peak_memory(void)
{
#ifdef _WIN32
    PROCESS_MEMORY_COUNTERS c;
    return GetProcessMemoryInfo(GetCurrentProcess(), &c, sizeof c) ? (double)c.PeakWorkingSetSize : 0;
#else
    struct rusage u;
    if (getrusage(RUSAGE_SELF, &u)) return 0;
#ifdef __APPLE__
    return (double)u.ru_maxrss;           /* bytes on macOS */
#else
    return 1024.0 * (double)u.ru_maxrss;  /* kilobytes on Linux */
#endif
#endif
}

/* Build a machine's tables from its plan: every transition is computed from the base table
 * (in parallel), then placed. */
typedef struct { Key next; Blocks *blocks; uint64_t syms; TopStep step; } Computed;
static void build_machine(Machine *M, unsigned height, uint32_t *chain, size_t nslots,
                          const PlanEntry *rows, size_t nrows, const PlanEntry *trans, size_t ntrans)
{
    M->height = height; M->chain = chain; M->nslots = (uint32_t)nslots;
    for (size_t r = 0; r < nrows; ++r) M->row[state_of_key(M, (Key)rows[r].hi << 64 | rows[r].lo)] = rows[r].x;
    M->state_at = (uint32_t *)malloc(nslots * 4);
    for (size_t i = 0; i < nslots; ++i) M->state_at[i] = UINT32_MAX;
    for (uint32_t s = 0; s < M->nstates; ++s) if (M->row[s] != UINT32_MAX) M->state_at[M->row[s]] = s;
    if (nslots + MAX_STATES + 256 >= 65535) die("too many slots for 16-bit rows:", nslots);
    for (size_t i = 0; i < nslots; ++i) chain[i] = 0xFFFF;  /* a tag no row has */
    Computed *c = (Computed *)calloc(ntrans, sizeof(Computed));
#pragma omp parallel for schedule(dynamic, 32)
    for (size_t k = 0; k < ntrans; ++k) {
        Blocks *bl = &scratch_blocks;
        if (!tower_step(height, (Key)trans[k].hi << 64 | trans[k].lo, trans[k].x, &c[k].next, bl)) die("a planned transition is rejected:", k);
        if (height == PAIR_HEIGHT) c[k].syms = pair_symbols(bl);
        else {
            c[k].step = top_step(bl);
            if (ROWS) { c[k].blocks = (Blocks *)malloc(sizeof(unsigned) * 2 + 2 * bl->n); c[k].blocks->n = bl->n; memcpy(c[k].blocks->slot, bl->slot, 2 * bl->n); }
        }
    }
    size_t pool = 0;
    if (ROWS && height == TOP_HEIGHT) {
        size_t total = 0;
        for (size_t k = 0; k < ntrans; ++k) total += c[k].blocks->n;
        top_block_lists = (uint16_t *)malloc(2 * total + 64);
    }
    for (size_t k = 0; k < ntrans; ++k) {
        uint32_t from = state_of_key(M, (Key)trans[k].hi << 64 | trans[k].lo), to = state_of_key(M, c[k].next);
        size_t x = M->row[from] + BYTE_CODES[trans[k].x];
        chain[x] = M->row[from] | row_of_state(M, to) << 16;
        if (height == PAIR_HEIGHT) PAIR_SYMBOLS[x] = c[k].syms;
        else {
            TOP_STEPS[x] = c[k].step;
            if (ROWS) {
                TOP_BLOCK_REFS[x] = pool | (uint64_t)c[k].blocks->n << 32;
                memcpy(top_block_lists + pool, c[k].blocks->slot, 2 * c[k].blocks->n);
                pool += c[k].blocks->n; free(c[k].blocks);
            }
        }
    }
    free(c);
}

/* The slow path: a transition not in the table, from the base table. Returns the next row;
 * the step's blocks are left in scratch_blocks. */
static uint32_t slow_step(Machine *M, uint64_t row, unsigned b)
{
    Key next;
    omp_set_lock(&slow_lock);
    uint32_t s = state_of_row(M, row);
    if (!tower_step(M->height, M->key[s], b, &next, &scratch_blocks)) die("an input byte is rejected by state", s);
    uint32_t r = row_of_state(M, state_of_key(M, next));
    slow_steps++;
    omp_unset_lock(&slow_lock);
    return r;
}
static uint32_t row_of_key(Machine *M, Key k)
{
    omp_set_lock(&slow_lock);
    uint32_t r = row_of_state(M, state_of_key(M, k));
    omp_unset_lock(&slow_lock);
    return r;
}
static Key key_of_row(Machine *M, uint64_t row)
{
    omp_set_lock(&slow_lock);
    Key k = M->key[state_of_row(M, row)];
    omp_unset_lock(&slow_lock);
    return k;
}

static uint8_t pair_seed_output[64]; static unsigned pair_seed_length;  /* what the seed pair has made */
static Key pair_seed_key;
static void train_plan(void);
static void build_tables(void)
{
    widen_entries();
    number_classes();
    size_t room = 65536;  /* slots: rows are 16-bit numbers */
    byte_code_table = (uint32_t *)reserve_at(BYTE_CODE, 256 * 4);
    power_table = (uint64_t *)reserve_at(POWER_OF_P, 65536 * 8);
    pair_chain_table = (uint32_t *)reserve_at(PAIR_CHAIN, room * 4);
    top_chain_table = (uint32_t *)reserve_at(TOP_CHAIN, room * 4);
    pair_symbol_table = (uint64_t *)reserve_at(PAIR_SYMS, room * 8);
    top_step_table = (TopStep *)reserve_at(TOP_STEP, room * 32);
    uint32_t *codes = BYTE_CODES;
    uint64_t *powers = POWERS;
    for (unsigned L = 0; L < 65536; ++L) powers[L] = L ? powers[L - 1] * P : 1;
    if (ROWS) {
        top_block_ref_table = (uint64_t *)reserve_at(TOP_BLOCKS, room * 8);
        for (unsigned i = 0; i < QF_SLOT_COUNT; ++i) {
            uint64_t e = entry[i];
            if (!LEN(e)) continue;
            for (unsigned j = 0; j < LEN(e); ++j) base_rows[i].code[j] = (int8_t)CODES(e)[j];
#if defined(__aarch64__)
            for (unsigned j = 0; j < LEN(e); ++j) { wide_rows[i].offset[j] = CODES(e)[j] & 127; wide_rows[i].upper[j] = -(uint64_t)(CODES(e)[j] >> 7); }
#endif
            base_rows[i].len = (uint8_t)LEN(e); base_rows[i].dm = (uint8_t)DM(e); base_rows[i].dnu = (uint8_t)(LEN(e) + DU(e));
        }
    }
    Blocks *bl = &scratch_blocks;
    pair_seed_key = tower_seed(PAIR_HEIGHT, bl);
    for (unsigned j = 0; j < bl->n; ++j)
        for (unsigned i = 0; i < LEN(entry[bl->slot[j]]); ++i) pair_seed_output[pair_seed_length++] = (uint8_t)symbol(SYMS(entry[bl->slot[j]]), i);
#if HAVE_PLAN
    for (unsigned b = 0; b < 256; ++b) codes[b] = plan_byte_code[b];
    build_machine(&pairs, PAIR_HEIGHT, PAIR_CHAINS, PLAN_PAIR_SLOTS, plan_pair_rows, PLAN_PAIR_ROWS, plan_pair_trans, PLAN_PAIR_TRANS);
    build_machine(&top, TOP_HEIGHT, TOP_CHAINS, PLAN_TOP_SLOTS, plan_top_rows, PLAN_TOP_ROWS, plan_top_trans, PLAN_TOP_TRANS);
#else
    (void)codes;
    train_plan();
#endif
    omp_init_lock(&slow_lock);
}


/* ======================================================================================
 * The chain below the top: pairs as copies
 *
 * Each pair (a tower of height 2) keeps its output, packed four symbols a byte, in a buffer
 * that the tower above reads. When the reader has used it up, `fill` refills it: it compacts
 * the buffer, refills the pair's own input first if needed (recursively, down the chain), and
 * runs the pair's steps. A group of four pairs (one from each of four chains) is filled in
 * lockstep, by the inner loops; a new pair's input is created on first use, starting from
 * the seed. Each level's budget is 3/8 of the one above (a pair's input advances 1/phi^2 as
 * fast as its output), so the whole chain is O(log N) bytes.
 * ====================================================================================== */
typedef struct Copy Copy;
struct Copy {
    Copy *in;               /* the pair below, whose output this one reads */
    uint32_t row;           /* its state, as a row of the pair table */
    uint32_t rd, end;       /* the reader is at byte rd; bytes rd .. end-1 are ready */
    uint32_t budget;        /* fill up to this many bytes */
    uint32_t bits;          /* 0-7 bits of a partial byte, in carry */
    uint64_t carry;
    uint8_t *buf;
};
#define TOP_BUDGET 16384u
#define MIN_BUDGET 8u
static inline uint32_t budget_below(uint32_t b) { uint32_t n = b * 3 / 8; return n > MIN_BUDGET ? n : MIN_BUDGET; }
static Copy *copy_new(uint32_t budget)
{
    Copy *c = (Copy *)calloc(1, sizeof(Copy));
    c->budget = budget;
    c->buf = (uint8_t *)aligned_alloc64(budget + 256);
    return c;
}
static void chain_free(Copy *c) { while (c) { Copy *below = c->in; aligned_free64(c->buf); free(c); c = below; } }
static inline void put_symbols(Copy *c, uint64_t syms, unsigned n)  /* n <= 28 */
{
    uint64_t pending = c->carry | (syms << c->bits);
    unsigned total = c->bits + 2 * n;
    memcpy(c->buf + c->end, &pending, 8);
    c->end += total >> 3; c->carry = pending >> (total & 56); c->bits = total & 7;
}
static Copy *seed_copy(uint32_t budget)
{
    Copy *c = copy_new(budget);
    put_symbols(c, QF_INITIAL_SYMBOLS & ((UINT64_C(1) << 36) - 1), 18);  /* sigma_30..47 */
    for (unsigned j = 0; j < pair_seed_length; ++j) put_symbols(c, pair_seed_output[j], 1);
    c->row = row_of_key(&pairs, pair_seed_key);
    return c;
}
static inline uint32_t ready(const Copy *c) { return c->end - c->rd; }

/* K steps of one pair, in C, with the slow path: for the rare transitions not in the table,
 * and for groups of fewer than four. */
static void pair_steps(Copy *c, uint32_t K)
{
    uint64_t row = c->row, carry = c->carry, bits = c->bits;
    uint8_t *out = c->buf + c->end;
    const uint8_t *in = c->in->buf + c->in->rd;
    for (uint32_t k = 0; k < K; ++k) {
        uint64_t x = row + BYTE_CODES[in[k]], w = PAIR_CHAINS[x], e = PAIR_SYMBOLS[x];
        if (__builtin_expect((w & 0xFFFF) == row, 1)) row = w >> 16;
        else { row = slow_step(&pairs, row, in[k]); e = pair_symbols(&scratch_blocks); }
        uint64_t pending = carry | ((e >> 8) << bits), total = bits + (e & 255);
        memcpy(out, &pending, 8);
        out += total >> 3; carry = pending >> (total & 56); bits = total & 7;
    }
    c->row = (uint32_t)row; c->carry = carry; c->bits = (uint32_t)bits;
    c->end = (uint32_t)(out - c->buf); c->in->rd += K;
}
#if SPIRE_X86  /* the inner loops, in loops.S */
uint32_t pair_chains4(uint64_t row[4], const uint8_t *const in[4], uint16_t *rec, uint32_t K);
void pair_pack2(uint64_t st0[3], uint64_t st1[3], const uint16_t *rec0, const uint16_t *rec1, uint32_t K);
uint32_t top_chains4(uint64_t row[4], const uint8_t *const in[4], uint16_t *rec, uint32_t K);
void top_hash2(uint64_t st0[3], uint64_t st1[3], const uint16_t *rec0, const uint16_t *rec1, uint32_t K);
#else          /* the same, in C */
#include "loops.c"
#endif
static __thread uint16_t records[4 * RECORDS_PER_CHAIN] __attribute__((aligned(64)));
/* K steps of n pairs: four at a time (chains first, then the symbols). */
static void pair_steps_n(Copy *const *c, int n, uint32_t K)
{
    if (n < 4) { for (int j = 0; j < n; ++j) pair_steps(c[j], K); return; }
    for (uint32_t done = 0; done < K;) {
        uint32_t want = K - done < RECORDS_PER_CHAIN ? K - done : RECORDS_PER_CHAIN;
        uint64_t row[4], st[4][3];
        const uint8_t *in[4];
        for (int j = 0; j < 4; ++j) {
            row[j] = c[j]->row; in[j] = c[j]->in->buf + c[j]->in->rd;
            st[j][0] = c[j]->carry; st[j][1] = c[j]->bits; st[j][2] = (uint64_t)(uintptr_t)(c[j]->buf + c[j]->end);
        }
        uint32_t k = pair_chains4(row, in, records, want);
        pair_pack2(st[0], st[1], records, records + RECORDS_PER_CHAIN, k);
        pair_pack2(st[2], st[3], records + 2 * RECORDS_PER_CHAIN, records + 3 * RECORDS_PER_CHAIN, k);
        for (int j = 0; j < 4; ++j) {
            c[j]->row = (uint32_t)row[j]; c[j]->carry = st[j][0]; c[j]->bits = (uint32_t)st[j][1];
            c[j]->end = (uint32_t)((uint8_t *)(uintptr_t)st[j][2] - c[j]->buf); c[j]->in->rd += k;
        }
        done += k;
        if (k < want) { for (int j = 0; j < 4; ++j) pair_steps(c[j], 1); ++done; }  /* not in the table */
    }
}
/* Fill n copies' buffers up to their budgets, in lockstep. */
static void fill(Copy *const *c, int n)
{
    for (int i = 0; i < n; ++i) {
        if (c[i]->rd) { memmove(c[i]->buf, c[i]->buf + c[i]->rd, c[i]->end - c[i]->rd); c[i]->end -= c[i]->rd; c[i]->rd = 0; }
        if (!c[i]->in) c[i]->in = seed_copy(budget_below(c[i]->budget));
    }
    for (;;) {
        Copy *active[8], *inputs[8];
        int na = 0, low = 0;
        uint32_t K = UINT32_MAX;
        for (int i = 0; i < n; ++i) {
            if (c[i]->end >= c[i]->budget) continue;
            uint32_t want = (c[i]->budget - c[i]->end) / 7;  /* a step makes at most 7 bytes */
            if (!want) want = 1;
            if (ready(c[i]->in) < want) low = 1;
            if (want < K) K = want;
            inputs[na] = c[i]->in; active[na++] = c[i];
        }
        if (!na) return;
        if (low) fill(inputs, na);
        for (int i = 0; i < na; ++i) if (ready(inputs[i]) < K) K = ready(inputs[i]);
        pair_steps_n(active, na, K);
    }
}
static inline unsigned next_byte(Copy *c)
{
    if (c->rd == c->end) fill(&c, 1);
    return c->buf[c->rd++];
}


/* ======================================================================================
 * Starting anywhere
 *
 * To start a copy near column A: its input copy is started a little before A/phi, the copy
 * reads 128 of its input symbols, keeping the records consistent with them; one record is
 * left (always within 58 symbols: synchronization.py), and the record gives m, n and U there:
 *     m = p - |Q|,  n = m + U(m-1) + z,  U(n-1) = m + w - |D|,  p the input position
 * (make_records.py checks these along the word).
 * The copy is then run one step at a time up to A. Copies run this way are "walkers"; a
 * tower is started as a stack of walkers, which are then read into the tower's state.
 * ====================================================================================== */
#define WARM 128u      /* input symbols read to find the record */
#define MARGIN 512u    /* start the input this many columns early, at least */
#define SMALL 16384u   /* below this column, start from the seed instead */
static unsigned U29;   /* the upper columns among 1..29 (the seed's) */
static int find_record(const uint8_t *win)
{
    static __thread uint8_t mark[REC_COUNT];
    int16_t set[REC_COUNT]; unsigned n = REC_COUNT;
    for (unsigned i = 0; i < n; ++i) set[i] = (int16_t)i;
    for (unsigned j = 0; j < WARM; ++j) {
        unsigned out = 0;
        for (unsigned i = 0; i < n; ++i) {
            int16_t t = rec_next[set[i]][win[j]];
            if (t >= 0 && !mark[t]) { mark[t] = 1; set[out++] = t; }
        }
        for (unsigned i = 0; i < out; ++i) mark[set[i]] = 0;
        n = out;
    }
    return n == 1 ? set[0] : -1;
}
typedef struct { unsigned cls; uint64_t n, m, U; } Start;  /* a copy's class and counters */
/* The state before input position p, from the WARM symbols before p and U(p-1). */
static Start start_at(const uint8_t *win, uint64_t p, uint64_t Up)
{
    int R = find_record(win);
    if (R < 0 || rec_base[R] < 0) die("no single record at column", p);
    Start st;
    st.m = p - rec_Qn[R];
    uint64_t Um = Up;  /* U(m-1): remove the upper columns m .. p-1, the window's last symbols */
    for (uint64_t x = st.m; x < p; ++x) Um -= win[WARM - (p - x)] >> 1;
    st.n = st.m + Um + (int64_t)rec_z[R];
    st.U = st.m + (int64_t)rec_w[R] - rec_Dn[R];
    st.cls = (unsigned)rec_base[R];
    return st;
}
static inline uint64_t input_start(uint64_t col) { return 30 + 4 * (div_phi(col - 48 - MARGIN) / 4); }

/* A walker: a single copy, one entry at a time. It reads either a pair (in) or another walker
 * (from); q[h .. t) is what it has made and its reader has not taken. */
typedef struct Walker Walker;
struct Walker { unsigned cls; uint64_t U; uint8_t q[QUEUE]; unsigned h, t; Copy *in; Walker *from; };
static unsigned walker_byte(Walker *w);
static inline unsigned walker_have(const Walker *w) { return w->t - w->h; }
static void walker_step(Walker *w)
{
    if (w->t + 16 > sizeof w->q) { memmove(w->q, w->q + w->h, w->t - w->h); w->t -= w->h; w->h = 0; }
    uint64_t e = entry[w->cls + (w->from ? walker_byte(w->from) : next_byte(w->in))];
    for (unsigned j = 0; j < LEN(e); ++j) w->q[w->t++] = (uint8_t)symbol(SYMS(e), j);
    w->cls = NEXT(e);
}
static unsigned walker_byte(Walker *w)  /* four symbols of its output, as a byte */
{
    while (walker_have(w) < 4) walker_step(w);
    unsigned b = w->q[w->h] | w->q[w->h + 1] << 2 | w->q[w->h + 2] << 4 | w->q[w->h + 3] << 6;
    w->h += 4;
    return b;
}
/* The next WARM symbols a walker makes, and U before the first of them + their uppers. */
static uint64_t walker_window(Walker *w, uint8_t *win)
{
    uint64_t U = w->U;
    for (unsigned j = 0; j < WARM; ++j) {
        if (!walker_have(w)) walker_step(w);
        win[j] = w->q[w->h++];
        U += win[j] >> 1;
    }
    return U;
}
/* Start a walker reading `in` (positioned at p - WARM, with U(p - WARM - 1) = Up) or `from`,
 * whose record is at input position p, so that its next output symbol is sigma_c. */
static void walker_start(Walker *w, Copy *in, Walker *from, uint64_t p, uint64_t Up, uint64_t c)
{
    uint8_t win[WARM];
    if (from) Up = walker_window(from, win);
    else for (unsigned j = 0; j < WARM / 4; ++j) {
        unsigned b = next_byte(in);
        Up += uppers(b);
        for (unsigned i = 0; i < 4; ++i) win[4 * j + i] = (uint8_t)symbol(b, i);
    }
    Start st = start_at(win, p, Up);
    if (st.n > c) die("a walker started past column", c);
    w->cls = st.cls; w->in = in; w->from = from; w->h = w->t = 0; w->U = st.U;
    for (uint64_t col = st.n; col < c; ++col) {
        if (!walker_have(w)) walker_step(w);
        w->U += w->q[w->h++] >> 1;
    }
}
/* A pair whose next output symbol is sigma_col (col = 30 mod 4), and U(col - 1). */
static Copy *start_pair(uint64_t col, uint32_t budget, uint64_t *U_before)
{
    if (col < SMALL) {
        Copy *c = seed_copy(budget);
        uint64_t U = U29;
        for (uint64_t cur = 30; cur < col; cur += 4) U += uppers(next_byte(c));
        *U_before = U;
        return c;
    }
    uint64_t p = input_start(col), q = input_start(p - WARM), Uq;
    Copy *in = start_pair(q - WARM, budget_below(budget), &Uq);
    Walker *mid = (Walker *)malloc(sizeof(Walker));  /* the pair's copy 1 */
    walker_start(mid, in, NULL, q, Uq, p - WARM);
    uint8_t win[WARM];
    Start st = start_at(win, p, walker_window(mid, win));
    if (st.n > col) die("a pair started past column", col);
    Copy *c = copy_new(budget);
    c->in = in;
    unsigned cls = st.cls;
    uint64_t U = st.U, cur = st.n;
    /* The pair's copy 0: to col, then on while copy 1 has four symbols pending. */
    while (cur < col || walker_have(mid) >= 4) {
        uint64_t e = entry[cls + walker_byte(mid)];
        unsigned len = LEN(e);
        uint64_t sy = SYMS(e);
        cls = NEXT(e);
        if (cur >= col) { put_symbols(c, sy, len); cur += len; continue; }
        if (cur + len <= col) { U += uppers(sy); cur += len; continue; }
        unsigned j0 = (unsigned)(col - cur);
        U += uppers(sy & ((UINT64_C(1) << (2 * j0)) - 1));
        put_symbols(c, sy >> (2 * j0), len - j0);
        cur += len;
    }
    Tower *t = &scratch_tower;  /* the pair's state */
    t->height = PAIR_HEIGHT; t->cls[0] = cls; t->cls[1] = mid->cls; t->h[0] = 0;
    t->n[0] = walker_have(mid); memcpy(t->q[0], mid->q + mid->h, t->n[0]);
    c->row = row_of_key(&pairs, tower_key(t));
    free(mid);
    *U_before = U;
    return c;
}


/* ======================================================================================
 * The top: the rows of a range [A, B)
 *
 * A run is the top tower of one range: its state (a row of the top table), its input (the
 * pair below it), the counters m, n + U and the column, and the hash (kept as (P - 1) H).
 * It starts as a stack of walkers (to A exactly), runs whole tower steps, and near B, where
 * the next step would pass B, finishes as walkers again (a short range is walked throughout).
 * With ROWS, every row is also written to a buffer of 1024 rows, which is summed (and, with
 * PRINT, printed) whenever it fills.
 * ====================================================================================== */
typedef struct {
    Copy *in;
    uint32_t row;
    uint64_t m, nu, col, A, B;   /* nu = n + U */
    uint64_t H, count, last;     /* H is (P - 1) times the hash */
    int done;
    uint64_t *rows; unsigned n;  /* rows written and not yet summed */
    uint64_t sum[4];             /* the rows summed so far, in four lanes */
    char *out; size_t outlen;    /* PRINT: the range's output so far */
} Run;
#define MAX_STEP_ROWS (12u * 2187u)  /* a step of a tower of 8: at most 3^7 blocks of 12 rows */
#define ROW_BUFFER 1024u

#if PRINT
/* The rows as text, one decimal number a line, or as 64-bit little-endian binary. */
static int print_binary;
static const char digit_pairs[] =
    "00010203040506070809101112131415161718192021222324252627282930313233343536373839"
    "40414243444546474849505152535455565758596061626364656667686970717273747576777879"
    "8081828384858687888990919293949596979899";
static inline char *put_decimal(char *p, uint64_t x)
{
    char digits[24], *d = digits + sizeof digits;
    while (x >= 100) { d -= 2; memcpy(d, digit_pairs + 2 * (x % 100), 2); x /= 100; }
    if (x >= 10) { d -= 2; memcpy(d, digit_pairs + 2 * x, 2); } else *--d = (char)('0' + x);
    size_t n = (size_t)(digits + sizeof digits - d);
    memcpy(p, d, n); p[n] = '\n';
    return p + n + 1;
}
static void print_rows(Run *r, const uint64_t *rows, unsigned k)
{
    if (print_binary) { memcpy(r->out + r->outlen, rows, 8 * (size_t)k); r->outlen += 8 * (size_t)k; return; }
    char *p = r->out + r->outlen;
    for (unsigned i = 0; i < k; ++i) p = put_decimal(p, rows[i]);
    r->outlen = (size_t)(p - r->out);
}
#endif

/* Sum the written rows (and print them), four at a time (eight with AVX-512 or on ARM64, into
 * independent sums); up to three stay at the front. */
static inline void sum_rows(Run *r)
{
    unsigned n = r->n, i = 0;
#if PRINT
    print_rows(r, r->rows, n & ~3u);
#endif
#if ROWS_AVX512
    __m512i s0 = _mm512_setzero_si512(), s1 = s0;
    for (; i + 16 <= n; i += 16) {
        s0 = _mm512_add_epi64(s0, _mm512_loadu_si512(r->rows + i));
        s1 = _mm512_add_epi64(s1, _mm512_loadu_si512(r->rows + i + 8));
    }
    __m512i s8 = _mm512_add_epi64(s0, s1);
    __m256i s = _mm256_add_epi64(_mm512_castsi512_si256(s8), _mm512_extracti64x4_epi64(s8, 1));
    s = _mm256_add_epi64(s, _mm256_loadu_si256((const __m256i *)r->sum));
    for (; i + 4 <= n; i += 4) s = _mm256_add_epi64(s, _mm256_loadu_si256((const __m256i *)(r->rows + i)));
    _mm256_storeu_si256((__m256i *)r->sum, s);
#elif ROWS_AVX2
    __m256i s = _mm256_loadu_si256((const __m256i *)r->sum);
    for (; i + 16 <= n; i += 16) {
        __m256i a = _mm256_add_epi64(_mm256_loadu_si256((const __m256i *)(r->rows + i)), _mm256_loadu_si256((const __m256i *)(r->rows + i + 4)));
        __m256i b = _mm256_add_epi64(_mm256_loadu_si256((const __m256i *)(r->rows + i + 8)), _mm256_loadu_si256((const __m256i *)(r->rows + i + 12)));
        s = _mm256_add_epi64(s, _mm256_add_epi64(a, b));
    }
    for (; i + 4 <= n; i += 4) s = _mm256_add_epi64(s, _mm256_loadu_si256((const __m256i *)(r->rows + i)));
    _mm256_storeu_si256((__m256i *)r->sum, s);
#elif defined(__aarch64__)
    uint64x2_t s0 = vld1q_u64(r->sum), s1 = vld1q_u64(r->sum + 2), s2 = vdupq_n_u64(0), s3 = s2;
    for (; i + 8 <= n; i += 8) {
        uint64x2x4_t a = vld1q_u64_x4(r->rows + i);
        s0 = vaddq_u64(s0, a.val[0]); s1 = vaddq_u64(s1, a.val[1]); s2 = vaddq_u64(s2, a.val[2]); s3 = vaddq_u64(s3, a.val[3]);
    }
    if (i + 4 <= n) { s0 = vaddq_u64(s0, vld1q_u64(r->rows + i)); s1 = vaddq_u64(s1, vld1q_u64(r->rows + i + 2)); i += 4; }
    vst1q_u64(r->sum, vaddq_u64(s0, s2)); vst1q_u64(r->sum + 2, vaddq_u64(s1, s3));
#else
    uint64_t s0 = r->sum[0], s1 = r->sum[1], s2 = r->sum[2], s3 = r->sum[3];
    for (; i + 4 <= n; i += 4) { s0 += r->rows[i]; s1 += r->rows[i + 1]; s2 += r->rows[i + 2]; s3 += r->rows[i + 3]; }
    r->sum[0] = s0; r->sum[1] = s1; r->sum[2] = s2; r->sum[3] = s3;
#endif
    for (unsigned j = 0; i < n; ++i, ++j) r->rows[j] = r->rows[i];
    r->n = n & 3;
}
/* Write the rows of a step's blocks, from m and n + U before it: row = (upper ? nu : m) +
 * offset. With AVX-512, eight rows per instruction (the codes' sign bits, the upper bits, become
 * a mask register that selects nu); with AVX2, four (a sign-extended code selects nu with a byte
 * blend and gives the offset with a mask); with NEON, two, from the widened codes. */
static inline void write_rows(Run *r, const uint16_t *slots, unsigned nblocks, uint64_t m, uint64_t nu)
{
#if ROWS_AVX512
    const __m128i low7 = _mm_set1_epi8(127);
#elif ROWS_AVX2
    const __m256i low7 = _mm256_set1_epi64x(127);
#endif
    uint64_t *buf = r->rows;
    unsigned n = r->n;
    for (unsigned j = 0; j < nblocks; ++j) {
        const BaseRows *b = &base_rows[slots[j]];
#if ROWS_AVX512
        __m128i code = _mm_loadu_si128((const __m128i *)b->code), offset = _mm_and_si128(code, low7);
        __mmask16 upper = _mm_movepi8_mask(code);  /* bits 12 to 15 (len, dm, ...) are not used */
        __m512i mv = _mm512_set1_epi64((long long)m), nv = _mm512_set1_epi64((long long)nu);
        _mm512_storeu_si512(buf + n, _mm512_add_epi64(_mm512_mask_blend_epi64((__mmask8)upper, mv, nv), _mm512_cvtepu8_epi64(offset)));
        _mm256_storeu_si256((__m256i *)(buf + n + 8), _mm256_add_epi64(_mm256_mask_blend_epi64((__mmask8)(upper >> 8), _mm512_castsi512_si256(mv), _mm512_castsi512_si256(nv)),
                                                                        _mm256_cvtepu8_epi64(_mm_srli_si128(offset, 8))));
#elif ROWS_AVX2
        const __m256i mv = _mm256_set1_epi64x((long long)m), nv = _mm256_set1_epi64x((long long)nu);
        for (unsigned g = 0; g < 3; ++g) {
            int32_t four; memcpy(&four, b->code + 4 * g, 4);
            __m256i code = _mm256_cvtepi8_epi64(_mm_cvtsi32_si128(four));
            _mm256_storeu_si256((__m256i *)(buf + n + 4 * g), _mm256_add_epi64(_mm256_blendv_epi8(mv, nv, code), _mm256_and_si256(code, low7)));
        }
#else
#if defined(__aarch64__)
        const WideRows *w = &wide_rows[slots[j]];
        const int64x2_t mv = vdupq_n_s64((int64_t)m), nv = vdupq_n_s64((int64_t)nu);
        for (unsigned g = 0; g < 12; g += 2)
            vst1q_s64((int64_t *)(buf + n + g), vaddq_s64(vbslq_s64(vld1q_u64(w->upper + g), nv, mv), vld1q_s64(w->offset + g)));
#else
        uint64_t d = nu - m;  /* all 12 rows are written; only the first len count */
        for (unsigned g = 0; g < 12; ++g) buf[n + g] = m + (d & -(uint64_t)(b->code[g] < 0)) + (uint64_t)(b->code[g] & 127);
#endif
#endif
        n += b->len; m += b->dm; nu += b->dnu;
        if (n >= ROW_BUFFER) { r->n = n; sum_rows(r); n = r->n; }
    }
    r->n = n;
}
static inline void write_step_rows(Run *r, uint64_t slot, uint64_t m, uint64_t nu)
{
    uint64_t ref = TOP_BLOCK_REFS[slot];
    write_rows(r, top_block_lists + (uint32_t)ref, (unsigned)(ref >> 32), m, nu);
}
/* One row made by walking (near the ends of a range). */
static inline void emit(Run *r, uint64_t y)
{
    r->H = r->H * P + (P - 1) * y; r->last = y; r->count++;
    if (ROWS) { r->rows[r->n++] = y; if (r->n >= ROW_BUFFER) sum_rows(r); }
}
/* The sum of a finished range's rows: the rest of the buffer summed (and printed). */
static uint64_t rows_total(Run *r)
{
    sum_rows(r);
#if PRINT
    print_rows(r, r->rows, r->n);
#endif
    uint64_t s = r->sum[0] + r->sum[1] + r->sum[2] + r->sum[3];
    for (unsigned q = 0; q < r->n; ++q) s += r->rows[q];
    r->n = 0;
    return s;
}

/* One block of the top copy, walking: the rows in [A, B) are emitted. */
static unsigned walk_block(Run *r, unsigned cls, unsigned byte)
{
    uint64_t e = entry[cls + byte];
    const uint8_t *codes = CODES(e);
    for (unsigned j = 0; j < LEN(e); ++j) {
        uint64_t c = r->col + j;
        if (c >= r->A && c < r->B) emit(r, (codes[j] >> 7 ? r->nu : r->m) + (codes[j] & 127));
    }
    r->col += LEN(e); r->m += DM(e); r->nu += LEN(e) + DU(e);
    return NEXT(e);
}
/* The input buffer of a range's top: the full budget for a long range, less for a short one,
 * which would not use it (a byte of the top's input stands for about 190 rows). */
static uint32_t top_budget(uint64_t rows) { return rows / 64 > TOP_BUDGET ? TOP_BUDGET : rows / 64 < 256 ? 256 : (uint32_t)(rows / 64); }
static void run_start(Run *r, uint64_t A, uint64_t B)
{
    uint64_t *rows = r->rows;
    char *out = r->out;
    memset(r, 0, sizeof *r);
    r->rows = rows; r->out = out; r->A = A; r->B = B;
    if (A >= B) { r->done = 1; return; }
    const uint32_t budget = top_budget(B - A);
    const int walk_all = B - A < 2 * (uint64_t)MAX_STEP_ROWS + 2;  /* too short for tower steps */
    Walker *w = (Walker *)malloc(TOP_HEIGHT * sizeof(Walker));  /* copies 1 .. 7 of the tower */
    unsigned cls;
    if (A < SMALL * 4) {
        /* From the very start: the seed's rows, then every copy at its first 18 symbols. */
        const uint8_t *first = qf_packets + QF_INITIAL_PACKET;
        for (uint64_t c = A; c < 48 && c < B; ++c)
            emit(r, c < 30 ? qf_seed_queens[c] : (first[3 + c - 30] >> 7 ? 30 + QF_INITIAL_UPPER : QF_INITIAL_M) + (first[3 + c - 30] & 127));
        r->col = 48; r->m = QF_INITIAL_M + first[1]; r->nu = 48 + QF_INITIAL_UPPER + first[2];
        cls = QF_INITIAL_STATE;
        for (unsigned i = 1; i < TOP_HEIGHT; ++i) {
            w[i].cls = QF_INITIAL_STATE; w[i].h = 0; w[i].t = QF_INITIAL_LENGTH;
            for (unsigned j = 0; j < QF_INITIAL_LENGTH; ++j) w[i].q[j] = (uint8_t)symbol(QF_INITIAL_SYMBOLS, j);
            w[i].from = i + 1 < TOP_HEIGHT ? &w[i + 1] : NULL;
            w[i].in = i + 1 < TOP_HEIGHT ? NULL : seed_copy(budget);
        }
    } else {
        /* p[i]: where copy i + 1 finds its record; the pair below starts before the last. */
        uint64_t p[TOP_HEIGHT], U;
        p[0] = input_start(A);
        for (unsigned i = 1; i < TOP_HEIGHT; ++i) p[i] = input_start(p[i - 1] - WARM);
        Copy *in = start_pair(p[TOP_HEIGHT - 1] - WARM, budget, &U);
        walker_start(&w[TOP_HEIGHT - 1], in, NULL, p[TOP_HEIGHT - 1], U, p[TOP_HEIGHT - 2] - WARM);
        for (unsigned i = TOP_HEIGHT - 2; i >= 1; --i) walker_start(&w[i], NULL, &w[i + 1], p[i], 0, p[i - 1] - WARM);
        uint8_t win[WARM];
        Start st = start_at(win, p[0], walker_window(&w[1], win));
        if (st.n > A) die("the top started past column", A);
        r->col = st.n; r->m = st.m; r->nu = st.n + st.U; cls = st.cls;
    }
    /* To A (or through a short range), then let each copy read what is pending, bottom up. */
    r->in = w[TOP_HEIGHT - 1].in;
    while (r->col < B && (r->col < A || walk_all)) cls = walk_block(r, cls, walker_byte(&w[1]));
    if (r->col >= B) { r->done = 1; free(w); return; }
    for (unsigned i = TOP_HEIGHT - 1; i >= 2; --i)
        while (walker_have(&w[i]) >= 4) walker_step(&w[i - 1]);
    while (r->col < B && walker_have(&w[1]) >= 4) cls = walk_block(r, cls, walker_byte(&w[1]));
    if (r->col >= B) { r->done = 1; free(w); return; }
    Tower *t = &scratch_tower;  /* the tower's state */
    t->height = TOP_HEIGHT; t->cls[0] = cls;
    for (unsigned i = 1; i < TOP_HEIGHT; ++i) {
        t->cls[i] = w[i].cls; t->h[i - 1] = 0;
        t->n[i - 1] = walker_have(&w[i]);
        memcpy(t->q[i - 1], w[i].q + w[i].h, t->n[i - 1]);
    }
    free(w);
    r->row = row_of_key(&top, tower_key(t));
}

/* K steps of one top tower, in C, with the slow path. */
static void run_steps(Run *r, uint32_t K)
{
    uint64_t row = r->row, m = r->m, nu = r->nu, H = r->H, col = r->col;
    const uint8_t *in = r->in->buf + r->in->rd;
    for (uint32_t k = 0; k < K; ++k) {
        uint64_t x = row + BYTE_CODES[in[k]], w = TOP_CHAINS[x];
        TopStep s;
        if (__builtin_expect((w & 0xFFFF) == row, 1)) {
            row = w >> 16; s = TOP_STEPS[x];
            if (ROWS) write_step_rows(r, x, m, nu);
        } else {
            row = slow_step(&top, row, in[k]); s = top_step(&scratch_blocks);
            if (ROWS) write_rows(r, scratch_blocks.slot, scratch_blocks.n, m, nu);
        }
        uint64_t L = s.lm & 0xFFFF, F = (H + m) * POWERS[L] + (nu - m) * s.b + s.c;
        col += L; m += s.lm >> 24; nu += s.dd + (s.lm >> 24); H = F - m;
    }
    r->count += col - r->col;
    r->row = (uint32_t)row; r->m = m; r->nu = nu; r->H = H; r->col = col; r->in->rd += K;
}
/* K steps of n top towers: four at a time (chains, then rows, then the hash). */
static void run_steps_n(Run *const *r, int n, uint32_t K)
{
    if (n < 4) { for (int j = 0; j < n; ++j) run_steps(r[j], K); return; }
    for (uint32_t done = 0; done < K;) {
        uint32_t want = K - done < RECORDS_PER_CHAIN ? K - done : RECORDS_PER_CHAIN;
        if (want > (1u << 24) / MAX_STEP_ROWS) want = (1u << 24) / MAX_STEP_ROWS;  /* columns in 24 bits */
        uint64_t row[4], st[4][3];
        const uint8_t *in[4];
        for (int j = 0; j < 4; ++j) {
            row[j] = r[j]->row; in[j] = r[j]->in->buf + r[j]->in->rd;
            st[j][0] = 0; st[j][1] = r[j]->nu - r[j]->m; st[j][2] = r[j]->H + r[j]->m;  /* M from 0 */
        }
        uint32_t k = top_chains4(row, in, records, want);
        if (ROWS)
            for (int j = 0; j < 4; ++j) {
                const uint16_t *rec = records + j * RECORDS_PER_CHAIN;
                uint64_t m = r[j]->m, nu = r[j]->nu;
                for (uint32_t i = 0; i < k; ++i) {
                    const TopStep *s = &TOP_STEPS[rec[i]];
                    write_step_rows(r[j], rec[i], m, nu);
                    m += s->lm >> 24; nu += s->dd + (s->lm >> 24);
                }
            }
        top_hash2(st[0], st[1], records, records + RECORDS_PER_CHAIN, k);
        top_hash2(st[2], st[3], records + 2 * RECORDS_PER_CHAIN, records + 3 * RECORDS_PER_CHAIN, k);
        for (int j = 0; j < 4; ++j) {
            uint64_t cols = st[j][0] & 0xFFFFFF;
            r[j]->row = (uint32_t)row[j]; r[j]->m += st[j][0] >> 24; r[j]->col += cols; r[j]->count += cols;
            r[j]->nu = r[j]->m + st[j][1]; r[j]->H = st[j][2] - r[j]->m; r[j]->in->rd += k;
        }
        done += k;
        if (k < want) { for (int j = 0; j < 4; ++j) run_steps(r[j], 1); ++done; }  /* not in the table */
    }
}
/* Near B: whole steps while the next one fits, then the rest walking. */
static void run_finish(Run *r)
{
    for (;;) {
        if (ready(r->in) == 0) fill(&r->in, 1);
        uint64_t x = r->row + BYTE_CODES[r->in->buf[r->in->rd]];
        if ((TOP_CHAINS[x] & 0xFFFF) != r->row || r->col + (TOP_STEPS[x].lm & 0xFFFF) > r->B) break;
        run_steps(r, 1);
    }
    Tower *t = &scratch_tower;
    tower_load(t, TOP_HEIGHT, key_of_row(&top, r->row));
    Walker *w = (Walker *)malloc(TOP_HEIGHT * sizeof(Walker));
    for (unsigned i = 1; i < TOP_HEIGHT; ++i) {
        w[i].cls = t->cls[i]; w[i].h = 0; w[i].t = t->n[i - 1];
        memcpy(w[i].q, t->q[i - 1], t->n[i - 1]);
        w[i].from = i + 1 < TOP_HEIGHT ? &w[i + 1] : NULL;
        w[i].in = i + 1 < TOP_HEIGHT ? NULL : r->in;
    }
    unsigned cls = t->cls[0];
    while (r->col < r->B) cls = walk_block(r, cls, walker_byte(&w[1]));
    free(w);
    r->done = 1;
}
/* A group of four ranges, run side by side until all are done. (Compiled on its own, not
 * inlined, so that the inner loops' use of registers does not depend on the caller.) */
#define GROUP 4
#define LOW_INPUT 64u
static __attribute__((noinline)) void run_group(Run *r)
{
    for (;;) {
        Run *active[GROUP]; Copy *inputs[GROUP];
        int na = 0, low = 0;
        for (int i = 0; i < GROUP; ++i) {
            if (!r[i].done && r[i].B - r[i].col < 2 * (uint64_t)MAX_STEP_ROWS + 2) run_finish(&r[i]);
            if (r[i].done) continue;
            if (ready(r[i].in) < LOW_INPUT) low = 1;
            inputs[na] = r[i].in; active[na++] = &r[i];
        }
        if (!na) break;
        if (low) fill(inputs, na);
        uint32_t K = UINT32_MAX;
        for (int i = 0; i < na; ++i) {
            uint64_t k = (active[i]->B - active[i]->col) / MAX_STEP_ROWS - 1;  /* cannot pass B */
            if (k < K) K = (uint32_t)k;
            if (ready(active[i]->in) < K) K = ready(active[i]->in);
        }
        run_steps_n(active, na, K);
    }
    for (int i = 0; i < GROUP; ++i) chain_free(r[i].in);
}


/* ======================================================================================
 * The plan (`spire-plan --plan`, which `make` runs, or at startup when plan.h is missing)
 *
 * Run each machine along sigma (2^24 symbols, made by the self-feeding loop), keeping the
 * transitions it meets; number the bytes by frequency (the columns of a row); order the
 * states by frequency and give each a row by first fit: the lowest offset where its columns
 * are free. The packing is dense (about 1.02 slots per transition), so the busy part of the
 * chain tables stays in the fast caches.
 * ====================================================================================== */
static int plan_mode;
static uint8_t *make_sigma(size_t n)  /* sigma_30, sigma_31, ...: one copy reading itself */
{
    uint8_t *s = (uint8_t *)malloc(n + 64);
    for (unsigned j = 0; j < QF_INITIAL_LENGTH; ++j) s[j] = (uint8_t)symbol(QF_INITIAL_SYMBOLS, j);
    size_t len = QF_INITIAL_LENGTH, r = 0;
    unsigned cls = QF_INITIAL_STATE;
    while (len < n) {
        uint64_t e = entry[cls + (s[r] | s[r + 1] << 2 | s[r + 2] << 4 | s[r + 3] << 6)];
        r += 4;
        for (unsigned j = 0; j < LEN(e); ++j) s[len++] = (uint8_t)symbol(SYMS(e), j);
        cls = NEXT(e);
    }
    return s;
}
static int by_count_desc(const void *a, const void *b)
{
    uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
    return x < y ? 1 : x > y ? -1 : 0;
}
typedef struct { PlanEntry *rows, *trans; size_t nrows, ntrans, nslots; } Plan;
static Plan train_machine(unsigned height, Key seed, const uint8_t *sigma, size_t n, const uint32_t *code)
{
    Machine *M = (Machine *)calloc(1, sizeof(Machine));  /* a scratch map for the training */
    M->height = height;
    uint32_t s = state_of_key(M, seed);
    int32_t **seen = (int32_t **)calloc(MAX_STATES, sizeof(int32_t *));
    uint64_t *visits = (uint64_t *)calloc(MAX_STATES, 8);
    Plan pl = {0};
    size_t cap = 1 << 15;
    pl.trans = (PlanEntry *)malloc(cap * sizeof(PlanEntry));
    uint32_t *to = (uint32_t *)malloc(cap * 4);
    for (size_t r = 0; r + 4 <= n - 64; r += 4) {
        unsigned b = sigma[r] | sigma[r + 1] << 2 | sigma[r + 2] << 4 | sigma[r + 3] << 6;
        visits[s]++;
        if (!seen[s]) { seen[s] = (int32_t *)malloc(256 * 4); for (unsigned i = 0; i < 256; ++i) seen[s][i] = -1; }
        if (seen[s][b] < 0) {
            Key next;
            if (!tower_step(height, M->key[s], b, &next, &scratch_blocks)) die("sigma is rejected at", r);
            if (pl.ntrans == cap) { cap *= 2; pl.trans = (PlanEntry *)realloc(pl.trans, cap * sizeof(PlanEntry)); to = (uint32_t *)realloc(to, cap * 4); }
            PlanEntry t = {(uint64_t)M->key[s], (uint64_t)(M->key[s] >> 64), b};
            pl.trans[pl.ntrans] = t; to[pl.ntrans] = state_of_key(M, next);
            seen[s][b] = (int32_t)pl.ntrans++;
        }
        s = to[seen[s][b]];
    }
    /* Rows by first fit, the busiest states first. */
    uint64_t *order = (uint64_t *)malloc(M->nstates * 8);
    size_t nrows = 0;
    for (uint32_t i = 0; i < M->nstates; ++i) if (seen[i]) order[nrows++] = visits[i] << 16 | (MAX_STATES - 1 - i);
    qsort(order, nrows, 8, by_count_desc);
    size_t cells = pl.ntrans + 256 * nrows + 512, lo = 0;
    uint8_t *used = (uint8_t *)calloc(cells, 1), *is_row = (uint8_t *)calloc(cells, 1);
    pl.rows = (PlanEntry *)malloc(nrows * sizeof(PlanEntry));
    for (size_t k = 0; k < nrows; ++k) {
        uint32_t id = MAX_STATES - 1 - (uint32_t)(order[k] & 0xFFFF);
        unsigned cols[256], nc = 0, least = 255;
        for (unsigned b = 0; b < 256; ++b) if (seen[id][b] >= 0) { cols[nc++] = code[b]; if (code[b] < least) least = code[b]; }
        while (used[lo]) ++lo;
        size_t o = lo > least ? lo - least : 0;
        for (;; ++o) {
            if (is_row[o]) continue;  /* rows start at distinct slots, so a row names its state */
            unsigned j = 0;
            while (j < nc && !used[o + cols[j]]) ++j;
            if (j == nc) break;
        }
        for (unsigned j = 0; j < nc; ++j) used[o + cols[j]] = 1;
        is_row[o] = 1;
        PlanEntry row = {(uint64_t)M->key[id], (uint64_t)(M->key[id] >> 64), (uint32_t)o};
        pl.rows[pl.nrows++] = row;
        if (o + 256 > pl.nslots) pl.nslots = o + 256;
    }
    for (uint32_t i = 0; i < MAX_STATES; ++i) free(seen[i]);
    free(seen); free(visits); free(order); free(used); free(is_row); free(to); free(M);
    return pl;
}
static void print_entries(const char *name, const PlanEntry *e, size_t n)
{
    printf("static const PlanEntry %s[%zu] = {", name, n);
    for (size_t k = 0; k < n; ++k)
        printf("%s%c{%lluu,%lluu,%u}", k ? "," : "", k % 4 ? ' ' : 10, (unsigned long long)e[k].lo, (unsigned long long)e[k].hi, e[k].x);
    printf("};%c", 10);
}
static __attribute__((unused)) void train_plan(void)
{
    size_t n = (size_t)1 << 24;
    uint8_t *sigma = make_sigma(n);
    uint64_t count[256] = {0}, order[256];
    for (size_t r = 0; r + 4 <= n - 64; r += 4) count[sigma[r] | sigma[r + 1] << 2 | sigma[r + 2] << 4 | sigma[r + 3] << 6]++;
    for (unsigned b = 0; b < 256; ++b) order[b] = count[b] << 8 | (255 - b);
    qsort(order, 256, 8, by_count_desc);
    uint32_t *code = BYTE_CODES;
    for (unsigned r = 0; r < 256; ++r) code[255 - (order[r] & 255)] = r;
    Blocks *bl = &scratch_blocks;
    Plan pp = train_machine(PAIR_HEIGHT, tower_seed(PAIR_HEIGHT, bl), sigma, n, code);
    Plan tp = train_machine(TOP_HEIGHT, tower_seed(TOP_HEIGHT, bl), sigma, n, code);
    free(sigma);
    if (plan_mode) {
        printf("/* Spire's plan: the states and transitions its tables hold (spire --plan). */%c", 10);
        printf("#define PLAN_PAIR_SLOTS %zuu%c#define PLAN_PAIR_ROWS %zuu%c#define PLAN_PAIR_TRANS %zuu%c", pp.nslots, 10, pp.nrows, 10, pp.ntrans, 10);
        printf("#define PLAN_TOP_SLOTS %zuu%c#define PLAN_TOP_ROWS %zuu%c#define PLAN_TOP_TRANS %zuu%c", tp.nslots, 10, tp.nrows, 10, tp.ntrans, 10);
        printf("static const uint8_t plan_byte_code[256] = {");
        for (unsigned b = 0; b < 256; ++b) printf("%s%u", b ? "," : "", code[b]);
        printf("};%c", 10);
        print_entries("plan_pair_rows", pp.rows, pp.nrows); print_entries("plan_pair_trans", pp.trans, pp.ntrans);
        print_entries("plan_top_rows", tp.rows, tp.nrows); print_entries("plan_top_trans", tp.trans, tp.ntrans);
        exit(0);
    }
    build_machine(&pairs, PAIR_HEIGHT, PAIR_CHAINS, pp.nslots, pp.rows, pp.nrows, pp.trans, pp.ntrans);
    build_machine(&top, TOP_HEIGHT, TOP_CHAINS, tp.nslots, tp.rows, tp.nrows, tp.trans, tp.ntrans);
}


/* ======================================================================================
 * main
 *
 * spire and spire-rows: the first N rows, as ranges in groups of four on all threads; the
 * checksum is combined over the ranges (H_total = H_total P^(rows of the next range) + H_next).
 * spire-print: the rows of [A, B), in pieces of four ranges, computed on all threads and
 * written in order. (spire-at is in spire-at.c.)
 * ====================================================================================== */
#define MAX_COLUMN UINT64_C(10000000000000000000)  /* 10^19: rows up to 1.62 10^19 fit in 64 bits */
/* H is (P - 1) times the checksum: halve it and divide by the odd (P - 1) / 2, mod 2^63. */
static uint64_t poly63(uint64_t H)
{
    uint64_t q = (P - 1) / 2, qinv = q;
    for (int i = 0; i < 6; ++i) qinv *= 2 - q * qinv;
    return ((H >> 1) * qinv) & (~UINT64_C(0) >> 1);
}
static void prepare(void)
{
    build_tables();
    for (unsigned x = 1; x < 30; ++x) U29 += qf_seed_queens[x] > x;
}

#if AT
/* spire-at.c has its own main. */

#elif PRINT
#define RANGE_ROWS (UINT64_C(1) << 17)  /* rows per range; four ranges make a piece */
int main(int argc, char **argv)
{
    uint64_t arg[3];
    int na = 0, count = 0;  /* count: B was written +k, for B = A + k */
    for (int i = 1; i < argc; ++i) {
        if (!strcmp(argv[i], "--binary")) print_binary = 1;
        else if (na == 1 && argv[i][0] == '+') count = 1, arg[na++] = parse_count(argv[i] + 1);
        else if (na < 3) arg[na++] = parse_count(argv[i]);
        else na = 4;
    }
    if (count && na >= 2) arg[1] = arg[1] > MAX_COLUMN ? UINT64_MAX : arg[0] + arg[1];
    if (na < 2 || na > 3 || arg[1] < arg[0] || arg[1] > MAX_COLUMN) {
        fprintf(stderr, "usage: spire-print A B [--binary] [threads]\n"
                        "  the rows q_A .. q_(B-1), A <= B <= 10^19 (B may be written +k, for A + k),\n"
                        "  one a line in decimal (or, with --binary, as 64-bit little-endian numbers)\n");
        return 2;
    }
    const uint64_t A = arg[0], B = arg[1];
    if (na == 3) omp_set_num_threads((int)arg[2]);
    int nthreads = omp_get_max_threads();
#ifdef _WIN32
    _setmode(_fileno(stdout), _O_BINARY);  /* the same bytes as elsewhere: no \r\n */
#endif
    double t0 = now();
    prepare();
    /* Room for a row: 8 bytes, or the digits of the largest row (below 2B + 64) and a newline. */
    size_t width = 8;
    if (!print_binary) { width = 2; for (unsigned __int128 x = (unsigned __int128)B * 2 + 64; x >= 10; x /= 10) ++width; }
    const uint64_t piece = GROUP * RANGE_ROWS, npieces = (B - A + piece - 1) / piece;
    uint64_t H = 0, total = 0, last = 0, sum = 0, bytes = 0;
#pragma omp parallel
    {
        Run *r = (Run *)aligned_alloc64(GROUP * sizeof(Run));
        uint64_t *rowbuf = (uint64_t *)aligned_alloc64(GROUP * 8 * (ROW_BUFFER + 64));
        char *outbuf = (char *)aligned_alloc64(GROUP * RANGE_ROWS * width + 64);
#pragma omp for ordered schedule(dynamic, 1)
        for (int64_t k = 0; k < (int64_t)npieces; ++k) {
            uint64_t sums[GROUP];
            for (int j = 0; j < GROUP; ++j) {
                uint64_t lo = A + (uint64_t)k * piece + j * RANGE_ROWS, hi = lo + RANGE_ROWS;
                r[j].rows = rowbuf + j * (ROW_BUFFER + 64);
                r[j].out = outbuf + j * RANGE_ROWS * width;
                run_start(&r[j], lo < B ? lo : B, hi < B ? hi : B);
            }
            run_group(r);
            for (int j = 0; j < GROUP; ++j) sums[j] = rows_total(&r[j]);
#pragma omp ordered
            for (int j = 0; j < GROUP; ++j) {
                if (r[j].outlen && fwrite(r[j].out, 1, r[j].outlen, stdout) != r[j].outlen) {
                    if (errno != EPIPE) perror("spire-print");  /* a closed pipe (| head) is no error */
                    exit(1);
                }
                H = H * power(P, r[j].count) + r[j].H;
                total += r[j].count; sum += sums[j]; bytes += r[j].outlen;
                if (r[j].count) last = r[j].last;
            }
        }
        aligned_free64(r); aligned_free64(rowbuf); aligned_free64(outbuf);
    }
    if (fflush(stdout)) { if (errno != EPIPE) perror("spire-print"); return 1; }
    if (total != B - A) die("rows made:", total);
    fprintf(stderr, "{\"A\":%llu,\"B\":%llu,\"format\":\"%s\",\"bytes\":%llu,\"threads\":%d,\"last\":%llu,"
                    "\"poly63\":\"%016llx\",\"rows_sum\":\"%016llx\",\"seconds\":%.3f,\"peak_mib\":%.1f}\n",
            (unsigned long long)A, (unsigned long long)B, print_binary ? "binary" : "text", (unsigned long long)bytes,
            nthreads, (unsigned long long)last, (unsigned long long)poly63(H), (unsigned long long)sum,
            now() - t0, peak_memory() / 1048576);
    return 0;
}

#else
typedef struct { uint64_t H, count, last, sum; } Result;
int main(int argc, char **argv)
{
    if (argc < 2) { fprintf(stderr, "usage: spire N [threads] [ranges]\n"); return 2; }
    if (!strcmp(argv[1], "--plan")) {
#if HAVE_PLAN
        fprintf(stderr, "spire: compile with -DTRAIN to regenerate the plan\n"); return 2;
#else
        plan_mode = 1; build_tables();
#endif
    }
    const uint64_t N = parse_count(argv[1]);
    if (N > MAX_COLUMN) die("N must be at most 10^19, not", N);
    if (argc > 2) omp_set_num_threads((int)parse_count(argv[2]));
    int nthreads = omp_get_max_threads();
    uint64_t nranges = argc > 3 ? parse_count(argv[3]) : 64;
    if (N < 1000000) nranges = GROUP;
    nranges = (nranges + GROUP - 1) / GROUP * GROUP;

    double t0 = now();
    prepare();
    double t1 = now();
    Result *res = (Result *)calloc(nranges, sizeof(Result));
#pragma omp parallel
    {
        Run *r = (Run *)aligned_alloc64(GROUP * sizeof(Run));
        uint64_t *rowbuf = (uint64_t *)aligned_alloc64(GROUP * 8 * (ROW_BUFFER + 64));
#pragma omp for schedule(dynamic, 1)
        for (int64_t i = 0; i < (int64_t)nranges; i += GROUP) {
            for (int j = 0; j < GROUP; ++j) {
                r[j].rows = rowbuf + j * (ROW_BUFFER + 64);
                run_start(&r[j], (uint64_t)((unsigned __int128)N * (uint64_t)(i + j) / nranges),
                                 (uint64_t)((unsigned __int128)N * (uint64_t)(i + j + 1) / nranges));
            }
            run_group(r);
            for (int j = 0; j < GROUP; ++j) {
                Result x = {r[j].H, r[j].count, r[j].last, rows_total(&r[j])};
                res[i + j] = x;
            }
        }
        aligned_free64(r); aligned_free64(rowbuf);
    }
    uint64_t H = 0, total = 0, last = 0, sum = 0;
    for (uint64_t i = 0; i < nranges; ++i) {
        H = H * power(P, res[i].count) + res[i].H;
        total += res[i].count; sum += res[i].sum;
        if (res[i].count) last = res[i].last;
    }
    double t2 = now();
    if (total != N) die("rows made:", total);
    printf("{\"N\":%llu,\"threads\":%d,\"ranges\":%llu,\"last\":%llu,\"poly63\":\"%016llx\"",
           (unsigned long long)N, nthreads, (unsigned long long)nranges, (unsigned long long)last, (unsigned long long)poly63(H));
    if (ROWS) printf(",\"rows_sum\":\"%016llx\"", (unsigned long long)sum);
    printf(",\"slow_steps\":%llu,\"setup\":%.3f,\"seconds\":%.3f,\"peak_mib\":%.1f}\n",
           (unsigned long long)slow_steps, t1 - t0, t2 - t0, peak_memory() / 1048576);
    return 0;
}
#endif
