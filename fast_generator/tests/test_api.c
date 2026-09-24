/* Test the public interface of src/queens_fast.h against the first million
 * rows of a full-occupancy calculation.
 *
 * Generator a fills arrays in chunks of varying sizes (including sizes that
 * stop inside a table block), b hashes the same chunks, d alternates between
 * hashing, filling and single rows on the same partly consumed block, and c
 * returns its first 10000 rows one at a time, interleaved with the others.
 * Every row, position and checksum is compared, and a few invalid calls are
 * checked. Build without -DNDEBUG: the checks are assertions.
 */
#include "../src/queens_fast.h"
#include <assert.h>
#include <errno.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#define N 1000000u
#define FNV0 UINT64_C(14695981039346656037)
#define FNV1 UINT64_C(1099511628211)

/* Complete occupancy reference; no local records, word graph, or tables. */
static uint64_t *reference(void)
{
    uint64_t *rows_out = malloc((size_t)N * sizeof(*rows_out));
    unsigned char *rows = calloc(2u*N+2u, 1), *diagonals = calloc(N+2u, 1);
    unsigned char *sums = calloc(3u*N+3u, 1);
    assert(rows_out && rows && diagonals && sums);
    unsigned m = 1, d = 1, upper = 0;
    rows[0] = sums[0] = 1;
    rows_out[0] = 0;
    for (unsigned n = 1; n < N; ++n) {
        unsigned y = m;
        while (y + d <= n && (rows[y] || diagonals[n-y] || sums[n+y])) ++y;
        if (y + d > n) y = n + ++upper;
        else {
            diagonals[n-y] = 1;
            while (diagonals[d]) ++d;
        }
        assert(!rows[y] && !sums[n+y]);
        rows[y] = sums[n+y] = 1;
        while (rows[m]) ++m;
        rows_out[n] = y;
    }
    free(rows); free(diagonals); free(sums);
    return rows_out;
}
int main(void)
{
    uint64_t *expected = reference();
    QFGenerator *a = qf_create(), *b = qf_create(), *c = qf_create(), *d = qf_create();
    assert(a && b && c && d);
    uint64_t buffer[8192], hash = FNV0, correct_hash = FNV0, last = 77;
    uint64_t mixed_hash = FNV0, mixed_last = 77;
    assert(qf_fill(a, NULL, 0) == 0 && qf_position(a) == 0);
    assert(qf_hash(b, 0, &hash, &last) == 0 && last == 77 && hash == FNV0);
    errno = 0;
    assert(qf_hash(b, UINT64_MAX, &hash, &last) == -1 && errno == ERANGE);
    assert(qf_position(b) == 0);
    static const unsigned chunks[] = {0,1,2,3,4,5,7,16,17,18,19,29,30,31,32,
                                     63,64,65,127,255,256,257,1023,1024,1025,4096,8191};
    unsigned position = 0, iteration = 0, third = 0;
    while (position < N) {
        unsigned size = chunks[iteration++ % (sizeof(chunks)/sizeof(chunks[0]))];
        if (size > N - position) size = N - position;
        assert(qf_fill(a, buffer, size) == 0);
        for (unsigned j = 0; j < size; ++j) {
            assert(buffer[j] == expected[position+j]);
            correct_hash = (correct_hash ^ buffer[j]) * FNV1;
        }
        assert(qf_hash(b, size, &hash, &last) == 0);
        /* Switch functions within the same partly consumed block. */
        if (iteration % 3u == 0) {
            assert(qf_hash(d, size, &mixed_hash, &mixed_last) == 0);
        } else {
            if (iteration % 3u == 1) assert(qf_fill(d, buffer, size) == 0);
            for (unsigned j = 0; j < size; ++j) {
                if (iteration % 3u == 2) assert(qf_next(d, buffer+j) == 0);
                assert(buffer[j] == expected[position+j]);
                mixed_last = buffer[j];
                mixed_hash = (mixed_hash ^ mixed_last) * FNV1;
            }
        }
        position += size;
        assert(qf_position(d) == position && mixed_hash == correct_hash);
        if (position) assert(mixed_last == expected[position-1u]);
        assert(qf_position(a) == position && qf_position(b) == position);
        assert(hash == correct_hash);
        if (position) assert(last == expected[position-1u]);
        if (third < 10000u) {
            uint64_t row;
            assert(qf_next(c, &row) == 0 && row == expected[third]);
            ++third;
        }
    }
    while (third < 10000u) {
        uint64_t row;
        assert(qf_next(c, &row) == 0 && row == expected[third++]);
    }
    QFStats sa = qf_stats(a), sb = qf_stats(b);
    assert(sa.levels == sb.levels && sa.heap_bytes == sb.heap_bytes);
    assert(qf_fill(a, NULL, 1) == -1 && errno == EINVAL);
    assert(qf_fill(NULL, buffer, 1) == -1 && errno == EINVAL);
    qf_destroy(a); qf_destroy(b); qf_destroy(c); qf_destroy(d); qf_destroy(NULL);
    free(expected);
    printf("{\"passed\":true,\"coordinate_comparisons\":%u,\"hash_resume_columns\":%u,"
           "\"interleaved_next_columns\":%u,\"chunk_calls\":%u,\"mixed_api_columns\":1000000,\"hash\":\"%016" PRIx64 "\"}\n",
           N, N, third, iteration, hash);
    return 0;
}
