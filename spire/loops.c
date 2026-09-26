/* Spire's inner loops in C, for processors other than x86-64 with AVX2 and BMI2 (on those,
 * loops.S is used instead). spire.c includes this file.
 *
 * They do exactly what the assembly does; see loops.S for the reasoning. On x86-64 the C
 * compiler could not keep four chains in its 15 registers, which is why the assembly exists;
 * ARM64 has 31, and there these loops keep every chain in a register as they are. The tables
 * are reached through pointers (BYTE_CODES and so on) instead of fixed addresses.
 */

/* K steps of four chains through `chain`, recording the slots; stops before the first step in
 * which a slot's tag is not the chain's row. Returns the number of steps done. */
static inline uint32_t chains4(const uint32_t *restrict chain, uint64_t row[4], const uint8_t *const in[4],
                               uint16_t *restrict rec, uint32_t K)
{
    const uint32_t *restrict code = BYTE_CODES;
    const uint8_t *i0 = in[0], *i1 = in[1], *i2 = in[2], *i3 = in[3];
    uint64_t r0 = row[0], r1 = row[1], r2 = row[2], r3 = row[3];
    uint32_t k;
    for (k = 0; k < K; ++k) {
        uint64_t x0 = r0 + code[i0[k]], x1 = r1 + code[i1[k]], x2 = r2 + code[i2[k]], x3 = r3 + code[i3[k]];
        uint32_t w0 = chain[x0], w1 = chain[x1], w2 = chain[x2], w3 = chain[x3];
        if (((w0 & 0xFFFF) != r0) | ((w1 & 0xFFFF) != r1) | ((w2 & 0xFFFF) != r2) | ((w3 & 0xFFFF) != r3)) break;
        rec[k] = (uint16_t)x0; rec[RECORDS_PER_CHAIN + k] = (uint16_t)x1;
        rec[2 * RECORDS_PER_CHAIN + k] = (uint16_t)x2; rec[3 * RECORDS_PER_CHAIN + k] = (uint16_t)x3;
        r0 = w0 >> 16; r1 = w1 >> 16; r2 = w2 >> 16; r3 = w3 >> 16;
    }
    row[0] = r0; row[1] = r1; row[2] = r2; row[3] = r3;
    return k;
}
static uint32_t pair_chains4(uint64_t row[4], const uint8_t *const in[4], uint16_t *rec, uint32_t K)
{
    return chains4(PAIR_CHAINS, row, in, rec, K);
}
static uint32_t top_chains4(uint64_t row[4], const uint8_t *const in[4], uint16_t *rec, uint32_t K)
{
    return chains4(TOP_CHAINS, row, in, rec, K);
}

/* The symbols of K recorded steps of two pairs, appended to their outputs (st = {carry,
 * bits, output pointer}): pending = carry | symbols << bits, stored whole; the output advances
 * by the complete bytes and the rest is carried. */
static void pair_pack2(uint64_t st0[3], uint64_t st1[3], const uint16_t *rec0, const uint16_t *rec1, uint32_t K)
{
    const uint64_t *restrict syms = PAIR_SYMBOLS;
    uint64_t c0 = st0[0], b0 = st0[1], c1 = st1[0], b1 = st1[1];
    uint8_t *o0 = (uint8_t *)(uintptr_t)st0[2], *o1 = (uint8_t *)(uintptr_t)st1[2];
    for (uint32_t k = 0; k < K; ++k) {
        uint64_t e0 = syms[rec0[k]], e1 = syms[rec1[k]];
        uint64_t p0 = c0 | ((e0 >> 8) << b0), t0 = b0 + (e0 & 255);
        uint64_t p1 = c1 | ((e1 >> 8) << b1), t1 = b1 + (e1 & 255);
        memcpy(o0, &p0, 8); memcpy(o1, &p1, 8);
        o0 += t0 >> 3; c0 = p0 >> (t0 & 56); b0 = t0 & 7;
        o1 += t1 >> 3; c1 = p1 >> (t1 & 56); b1 = t1 & 7;
    }
    st0[0] = c0; st0[1] = b0; st0[2] = (uint64_t)(uintptr_t)o0;
    st1[0] = c1; st1[1] = b1; st1[2] = (uint64_t)(uintptr_t)o1;
}

/* K recorded steps of two top towers (st = {M = m << 24 | columns, D = (n + U) - m,
 * F = (P - 1) H + m}): F <- F P^L + D (P-1) B + (P-1) C + dm, M += dm << 24 | L,
 * D += dnu - dm. */
static void top_hash2(uint64_t st0[3], uint64_t st1[3], const uint16_t *rec0, const uint16_t *rec1, uint32_t K)
{
    const TopStep *restrict steps = TOP_STEPS;
    const uint64_t *restrict powers = POWERS;
    uint64_t M0 = st0[0], D0 = st0[1], F0 = st0[2], M1 = st1[0], D1 = st1[1], F1 = st1[2];
    for (uint32_t k = 0; k < K; ++k) {
        const TopStep *s0 = &steps[rec0[k]], *s1 = &steps[rec1[k]];
        F0 = F0 * powers[s0->lm & 0xFFFF] + D0 * s0->b + s0->c; M0 += s0->lm; D0 += s0->dd;
        F1 = F1 * powers[s1->lm & 0xFFFF] + D1 * s1->b + s1->c; M1 += s1->lm; D1 += s1->dd;
    }
    st0[0] = M0; st0[1] = D0; st0[2] = F0;
    st1[0] = M1; st1[1] = D1; st1[2] = F1;
}
