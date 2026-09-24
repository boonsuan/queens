/* Scan the one-based sequence s(c)=q_(c-1)+1. Counts include the origin.
 *
 * This is the check of Knuth's ranges in the remark on 1-indexed
 * coordinates in Section 3 of the paper: every point must lie in
 * [c/phi-3, c/phi+5] or in [c*phi-2, c*phi+1]. The scanner checks this
 * union and, separately, the lower interval for lower queens (s < c) and the
 * upper interval for upper queens (s > c), and records the least and
 * greatest deviations s-c/phi and s-c*phi with the queens attaining them.
 * The rows come from qf_fill in batches of QF_SCAN_BATCH; they are also
 * folded into the checksum of queens_fast.
 *
 * Every membership test and extremum decision is mathematically exact.
 * Ordinary double arithmetic is a FILTER, never the final authority for
 * close comparisons. For c<=N<=10^11, s<=2*N+1, and rounding to nearest,
 * each computed deviation has absolute error < E=N*2^-50+2^-48:
 *  (i) the hexadecimal slope constants err by <2^-52;
 * (ii) the rounded product errs by <2^-52*N;
 *(iii) the rounded subtraction errs by <2^-51*N+2^-52.
 * These conservative bounds also cover contraction to a fused multiply-add.
 * Thus comparisons separated by E (two deviations: 2E) are certified.
 * Filter cutoffs are rounded outward using nextafter, including the
 * stronger sufficient thresholds for accepting interval membership.
 * Other comparisons use the exact integer sign of a-b*sqrt(5), in
 * bounds_exact.h. Do not compile with -ffast-math.
 *
 * Decimal extrema are only presentation: their witness coordinates specify
 * exact algebraic values. See print_witness for their error bound.
 */
#include "queens_fast.h"
#include "bounds_exact.h"
#include <errno.h>
#include <fenv.h>
#include <float.h>
#include <inttypes.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#if FLT_RADIX != 2 || DBL_MANT_DIG != 53
#error "The filtering proof requires IEEE binary64 double arithmetic."
#endif
#ifdef __FAST_MATH__
#error "Do not use fast-math for certified comparisons."
#endif
#define MAX_COUNT UINT64_C(100000000000)
#ifndef QF_SCAN_BATCH
#define QF_SCAN_BATCH 1024
#endif

typedef struct {
    uint64_t c, s;
    double approximate, near_cutoff, clear_cutoff;
} Witness;
typedef struct {
    uint64_t count, violations;
    Witness minimum, maximum, first_violation;
} Branch;
typedef struct {
    Branch upper, lower;
    uint64_t count, last, hash, union_violations, exact_comparisons;
    Witness first_union_violation;
    double error;
    double lower_lo, lower_hi, upper_lo, upper_hi;
    clock_t started;
    struct timespec wall_started;
} Scan;

static int parse_integer(const char *text, uint64_t *value)
{
    if (!text[0]) return -1;
    for (const char *p = text; *p; ++p)
        if (*p < '0' || *p > '9') return -1;
    char *end;
    errno = 0;
    unsigned long long result = strtoull(text, &end, 10);
    if (errno || *end || result > MAX_COUNT) return -1;
    *value = (uint64_t)result;
    return 0;
}

static void set_witness(Witness *w, uint64_t c, uint64_t s, double value,
                        double error, int minimum)
{
    w->c = c; w->s = s; w->approximate = value;
    w->near_cutoff = nextafter(value + (minimum ? 2 * error : -2 * error),
                               minimum ? INFINITY : -INFINITY);
    w->clear_cutoff = nextafter(value + (minimum ? -2 * error : 2 * error),
                                minimum ? -INFINITY : INFINITY);
}

static int inside_exact(Scan *scan, uint64_t c, uint64_t s, int upper)
{
    scan->exact_comparisons += 2;
    int low = bounds_threshold(c, s, upper, upper ? -2 : -3);
    int high = bounds_threshold(c, s, upper, upper ? 1 : 5);
    return low >= 0 && high <= 0;
}

static void process(Scan *scan, uint64_t c, uint64_t s)
{
    if (c == 1) {
        /* q_0=0 => s(1)=1: both intervals contain this point. */
        if (!inside_exact(scan, c, s, 0) && !inside_exact(scan, c, s, 1)) {
            ++scan->union_violations;
            set_witness(&scan->first_union_violation, c, s, 0, scan->error, 1);
        }
        return;
    }
    int upper = s > c;
    Branch *b = upper ? &scan->upper : &scan->lower;
    const double slope = upper ? 0x1.9e3779b97f4a8p+0 : 0x1.3c6ef372fe950p-1;
    double value = (double)s - slope * (double)c;
    if (!b->count) {
        set_witness(&b->minimum, c, s, value, scan->error, 1);
        set_witness(&b->maximum, c, s, value, scan->error, 0);
    } else {
        if (value < b->minimum.near_cutoff) {
            int smaller = value < b->minimum.clear_cutoff;
            if (!smaller) {
                ++scan->exact_comparisons;
                smaller = bounds_compare(c, s, b->minimum.c, b->minimum.s, upper) < 0;
            }
            if (smaller) set_witness(&b->minimum, c, s, value, scan->error, 1);
        }
        if (value > b->maximum.near_cutoff) {
            int larger = value > b->maximum.clear_cutoff;
            if (!larger) {
                ++scan->exact_comparisons;
                larger = bounds_compare(c, s, b->maximum.c, b->maximum.s, upper) > 0;
            }
            if (larger) set_witness(&b->maximum, c, s, value, scan->error, 0);
        }
    }
    ++b->count;
    const double low = upper ? scan->upper_lo : scan->lower_lo;
    const double high = upper ? scan->upper_hi : scan->lower_hi;
    if (!(value >= low && value <= high) && !inside_exact(scan, c, s, upper)) {
        if (!b->violations) set_witness(&b->first_violation, c, s, value, scan->error, 1);
        ++b->violations;
        if (!inside_exact(scan, c, s, !upper)) {
            if (!scan->union_violations)
                set_witness(&scan->first_union_violation, c, s, value, scan->error, 1);
            ++scan->union_violations;
        }
    }
}

static void print_witness(FILE *out, const Witness *w, int upper)
{
    if (!w->c) { fputs("null", out); return; }
    /* floor(sqrt(5)*2^80), checked by integer squaring in the tests.
     * Replacing sqrt(5) by this value changes the deviation by <c/2^81.
     * Cancellation happens in exact 128-bit integers BEFORE conversion to
     * long double. The printed error bound also covers conversion and
     * 12-place rounding, even for an unexpectedly large deviation.
     */
    const bounds_u128 sqrt5_x80 = ((bounds_u128)UINT64_C(146542) << 64) |
                                 UINT64_C(0xf372fe94f82be739);
    bounds_i128 residual = (bounds_i128)bounds_a(w->c, w->s, upper) *
                            ((bounds_i128)1 << 80) -
                            (bounds_i128)((bounds_u128)w->c * sqrt5_x80);
    long double value = (long double)residual / 0x1p81L;
    long double display_error = 2 * (w->c / 0x1p81L +
                                    fabsl(value) * LDBL_EPSILON + 5e-13L);
    fprintf(out, "{\"c\":%" PRIu64 ",\"s\":%" PRIu64
                 ",\"deviation\":%.12Lf,\"display_error_bound\":%.9Le}",
            w->c, w->s, value, display_error);
}

static void print_branch(FILE *out, const Branch *b, int upper)
{
    fprintf(out, "{\"count\":%" PRIu64 ",\"minimum\":", b->count);
    print_witness(out, &b->minimum, upper);
    fputs(",\"maximum\":", out); print_witness(out, &b->maximum, upper);
    fprintf(out, ",\"branch_interval_violations\":%" PRIu64
                 ",\"first_branch_violation\":", b->violations);
    print_witness(out, &b->first_violation, upper);
    fputc('}', out);
}

static int report(FILE *out, const Scan *scan, QFGenerator *g, int final)
{
    QFStats stats = qf_stats(g);
    struct timespec now;
    timespec_get(&now, TIME_UTC);
    double wall = now.tv_sec - scan->wall_started.tv_sec +
                  (now.tv_nsec - scan->wall_started.tv_nsec) * 1e-9;
    fprintf(out, "{\"algorithm\":\"queens-fast-certified-bounds\",\"final\":%s"
                 ",\"count\":%" PRIu64 ",\"last_column\":", final ? "true" : "false", scan->count);
    if (scan->count) fprintf(out, "%" PRIu64 ",\"last_queen\":%" PRIu64,
                             scan->count - 1, scan->last);
    else fputs("null,\"last_queen\":null", out);
    fprintf(out, ",\"hash\":\"%016" PRIx64 "\",\"upper\":", scan->hash);
    print_branch(out, &scan->upper, 1);
    fputs(",\"lower\":", out); print_branch(out, &scan->lower, 0);
    fprintf(out, ",\"origin_count\":%d,\"union_violations\":%" PRIu64
                 ",\"first_union_violation\":", scan->count ? 1 : 0, scan->union_violations);
    print_witness(out, &scan->first_union_violation,
                   scan->first_union_violation.s > scan->first_union_violation.c);
    fprintf(out, ",\"exact_comparisons\":%" PRIu64 ",\"screen_error_bound\":%.17g"
                 ",\"levels\":%zu"
                 ",\"generator_heap_bytes\":%zu,\"generator_static_bytes\":%zu"
                 ",\"scanner_buffer_bytes\":%zu,\"cpu_seconds\":%.9f"
                 ",\"wall_seconds\":%.9f}\n", scan->exact_comparisons, scan->error,
            stats.levels, stats.heap_bytes, stats.static_data_bytes,
            (size_t)QF_SCAN_BATCH * sizeof(uint64_t),
            (double)(clock() - scan->started) / CLOCKS_PER_SEC, wall);
    return fflush(out) || ferror(out);
}

int main(int argc, char **argv)
{
    uint64_t count = 0, progress = 0;
    int have_count = 0, have_progress = 0;
    for (int i = 1; i < argc; ++i) {
        if (!strcmp(argv[i], "--count") && i + 1 < argc && !have_count) {
            if (parse_integer(argv[++i], &count)) goto usage;
            have_count = 1;
        } else if (!strcmp(argv[i], "--progress-every") && i + 1 < argc && !have_progress) {
            if (parse_integer(argv[++i], &progress) || !progress) goto usage;
            have_progress = 1;
        } else goto usage;
    }
    if (!have_count) goto usage;
    if (fegetround() != FE_TONEAREST) {
        fputs("round-to-nearest arithmetic is required\n", stderr); return 1;
    }
    Scan scan = {0};
    scan.hash = UINT64_C(14695981039346656037);
    scan.error = nextafter((double)count * 0x1p-50 + 0x1p-48, INFINITY);
    scan.lower_lo = nextafter(-3 + scan.error, INFINITY);
    scan.lower_hi = nextafter(5 - scan.error, -INFINITY);
    scan.upper_lo = nextafter(-2 + scan.error, INFINITY);
    scan.upper_hi = nextafter(1 - scan.error, -INFINITY);
    scan.started = clock(); timespec_get(&scan.wall_started, TIME_UTC);
    QFGenerator *g = qf_create();
    if (!g) { perror("qf_create"); return 1; }
    uint64_t rows[QF_SCAN_BATCH];
    uint64_t next_progress = progress ? progress : count;
    while (scan.count < count) {
        uint64_t available = count - scan.count;
        if (progress && next_progress - scan.count < available)
            available = next_progress - scan.count;
        size_t batch = available < QF_SCAN_BATCH ? (size_t)available : QF_SCAN_BATCH;
        if (qf_fill(g, rows, batch)) { perror("qf_fill"); qf_destroy(g); return 1; }
        for (size_t i = 0; i < batch; ++i) {
            uint64_t c = scan.count + i + 1, s = rows[i] + 1;
            if (!s || s > 2 * count + 1 || (c > 1 && s == c) || (c == 1 && s != 1)) {
                fputs("generator coordinate outside scanner domain\n", stderr);
                qf_destroy(g); return 1;
            }
            scan.hash = (scan.hash ^ rows[i]) * UINT64_C(1099511628211);
            process(&scan, c, s);
        }
        scan.last = rows[batch - 1]; scan.count += batch;
        if (progress && scan.count == next_progress && scan.count < count) {
            if (report(stderr, &scan, g, 0)) { qf_destroy(g); return 1; }
            next_progress += progress;
        }
    }
    int failed = report(stdout, &scan, g, 1);
    qf_destroy(g);
    return failed ? 1 : 0;
usage:
    fprintf(stderr, "Usage: %s --count N [--progress-every K] (N <= 10^11)\n", argv[0]);
    return 2;
}
