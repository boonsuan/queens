/* Exact greedy-queen rows q_0, q_1, q_2, ... (Section 7 of the paper).
 *
 * Each QFGenerator is an independent, resumable generator; the fixed tables
 * are shared and read-only. Every call continues where the previous call on
 * the same generator stopped, so the three output functions can be mixed.
 *
 * Counts include the origin: after generating N rows, the last column is
 * N-1. Columns are limited to [0, UINT64_MAX/2).
 *
 * The generation functions return 0 on success and -1 with errno set on
 * failure: EINVAL for a bad argument or an unusable generator, ERANGE past
 * the column limit, and the allocator's error if a new copy of the
 * calculation cannot be allocated. After an allocation failure the
 * generator is unusable: destroy it.
 */
#ifndef QUEENS_FAST_H
#define QUEENS_FAST_H
#include <stddef.h>
#include <stdint.h>

typedef struct QFGenerator QFGenerator;

/* Storage accounting, reported by qf_stats. */
typedef struct {
    size_t levels;                 /* The outer copy plus the inner copies. */
    size_t generator_bytes;        /* The outer copy's record. */
    size_t producer_record_bytes;  /* One inner copy's record, without its buffer. */
    size_t symbol_buffer_bytes;    /* All ready-byte buffers, including padding. */
    size_t heap_bytes;             /* Total requested heap, without malloc overhead. */
    size_t static_data_bytes;      /* Table, coordinate data and seed rows;
                                      assertion builds add a lookup check array. */
    uint64_t outer_macro_steps;    /* Table lookups by the outer copy, */
    uint64_t inner_macro_steps;    /* by the inner copies, */
    uint64_t refill_calls;         /* and buffer refills; all three are zero
                                      unless compiled with -DQF_INSTRUMENT. */
} QFStats;

/* Create a generator positioned at column 0, or return NULL. */
QFGenerator *qf_create(void);

/* Free a generator and all of its copies. NULL is allowed. */
void qf_destroy(QFGenerator *generator);

/* The next column to be generated (0 for NULL). */
uint64_t qf_position(const QFGenerator *generator);

/* Store the next row in *row. */
int qf_next(QFGenerator *generator, uint64_t *row);

/* Store the next count rows in rows[0..count-1]. rows may be NULL only
 * when count is 0. */
int qf_fill(QFGenerator *generator, uint64_t *rows, size_t count);

/* Generate the next count rows without storing them. For each row y,
 * replace *hash by (*hash XOR y) * 1099511628211 modulo 2^64, and set *last
 * to y. The usual starting value of *hash is 14695981039346656037. When
 * count is 0, *hash and *last are left unchanged. */
int qf_hash(QFGenerator *generator, uint64_t count, uint64_t *hash, uint64_t *last);

/* Storage used so far by this generator. */
QFStats qf_stats(const QFGenerator *generator);
#endif
