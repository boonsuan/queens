#ifndef BOUNDS_EXACT_H
#define BOUNDS_EXACT_H
#include <stdint.h>

/* The scan is restricted to c <= 10^11 and 0 <= s <= 2*10^11+1.
 * All a,b below then have magnitude < 10^12; their squared magnitudes,
 * including the factor 5, fit comfortably in unsigned 128-bit integers.
 * GCC and Clang provide this extension; the generator itself remains C11.
 */
__extension__ typedef unsigned __int128 bounds_u128;
__extension__ typedef __int128 bounds_i128;

/* Exact sign of a-b*sqrt(5). Squaring is used only after checking signs. */
static int bounds_sign(int64_t a, int64_t b)
{
    if (!b) return (a > 0) - (a < 0);
    if (!a) return b < 0 ? 1 : -1;
    if (a > 0 && b < 0) return 1;
    if (a < 0 && b > 0) return -1;
    uint64_t aa = (uint64_t)(a < 0 ? -a : a);
    uint64_t bb = (uint64_t)(b < 0 ? -b : b);
    bounds_u128 left = (bounds_u128)aa * aa;
    bounds_u128 right = 5 * (bounds_u128)bb * bb;
    int order = (left > right) - (left < right);
    return a > 0 ? order : -order;
}

static int64_t bounds_a(uint64_t c, uint64_t s, int upper)
{
    return 2 * (int64_t)s + (upper ? -(int64_t)c : (int64_t)c);
}

/* Compare deviations s-alpha*c; alpha is phi for upper, 1/phi for lower. */
static int bounds_compare(uint64_t c, uint64_t s,
                          uint64_t other_c, uint64_t other_s, int upper)
{
    return bounds_sign(bounds_a(c, s, upper) - bounds_a(other_c, other_s, upper),
                       (int64_t)c - (int64_t)other_c);
}

static int bounds_threshold(uint64_t c, uint64_t s, int upper, int threshold)
{
    return bounds_sign(bounds_a(c, s, upper) - 2 * (int64_t)threshold,
                       (int64_t)c);
}

#endif
