/* The reference for Spire's checks: the first N rows from the Section 7 generator
 * (../fast_generator), one at a time, with the same checksums Spire reports:
 *   poly63  H = sum of q_n P^(N-1-n) mod 2^64, P = 1099511628211, printed modulo 2^63;
 *   sum     the sum of the rows mod 2^64;
 *   last    the last row.
 *
 *   reference N
 */
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include "queens_fast.h"

int main(int argc, char **argv)
{
    if (argc != 2) { fprintf(stderr, "usage: reference N\n"); return 2; }
    uint64_t N = strtoull(argv[1], NULL, 10), H = 0, sum = 0, last = 0;
    static uint64_t rows[1 << 16];
    QFGenerator *g = qf_create();
    if (!g) { perror("qf_create"); return 1; }
    for (uint64_t done = 0; done < N;) {
        size_t k = N - done < (1u << 16) ? (size_t)(N - done) : (size_t)1 << 16;
        if (qf_fill(g, rows, k)) { perror("qf_fill"); return 1; }
        for (size_t i = 0; i < k; ++i) { H = H * UINT64_C(1099511628211) + rows[i]; sum += rows[i]; }
        last = rows[k - 1];
        done += k;
    }
    qf_destroy(g);
    printf("{\"N\":%" PRIu64 ",\"last\":%" PRIu64 ",\"poly63\":\"%016" PRIx64 "\",\"rows_sum\":\"%016" PRIx64 "\"}\n",
           N, last, H & (~UINT64_C(0) >> 1), sum);
    return 0;
}
