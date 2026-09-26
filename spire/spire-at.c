/* spire-at: single rows q_n, each computed on its own, for n up to about 10^1150.
 *
 *     spire-at n [n ...]       or   spire-at -   (the n from standard input)
 *     spire-at --walk D n ...  (a check: the same rows, from chains aimed D columns earlier)
 *
 * For each n it prints q_n, whether the queen is upper (q_n near n phi) or lower (near n / phi),
 * and how far q_n is from that. Numbers may be written 12345, 1e100 or 10^100.
 *
 * THE IDEA. The queen word sigma is made by a chain of copies of one calculation, each reading
 * the output of the copy below it (the paper, Section 7): the copy that writes the columns near
 * n reads sigma only near n / phi, the copy below it only near n / phi^2, and so on. Between two
 * input bytes, a copy's whole state is one of 300 "paused records", and it can be recovered from
 * the input alone: start from the set of all 300, follow each on the input symbols, and drop
 * those that cannot read them. When one is left, it is the copy's true state, and the paper's
 * identities give the copy's counters there exactly (the least unused row m, the column n, and
 * the number U of upper columns before it), from its input position p:
 *     m = p - |Q|,    n = m + U(m-1) + z,    U(n-1) = m + w - |D|.
 *
 * So q_n needs only short pieces of sigma, near n / phi, n / phi^2, ...: the program starts one
 * copy for each, from the bottom (a prefix of sigma, made directly) up, each copy reading 128
 * symbols of the one below to find its record and then walking a few hundred columns to where
 * the copy above needs it. That is about log_phi n copies (some 480 for n = 10^100), each doing
 * about the same work; no row before q_n is ever made.
 *
 * The numbers are as large as n, but they are only ever compared, moved by small amounts, or
 * divided by phi. So they are kept as integers of many 64-bit words ("Big"), and 1/phi is
 * computed to 4 224 bits at the start, from the integer square root of 5. The base table, the
 * records and the prefix of sigma come from spire.c.
 */
#define AT 1
#pragma GCC diagnostic ignored "-Wunused-function"  /* spire-at uses only part of spire.c */
#pragma GCC diagnostic ignored "-Wunused-variable"
#include "spire.c"
#include <ctype.h>

/* ======================================================================================
 * Big integers: BIG_WORDS words of 64 bits, least significant first, and only what the copies
 * need: add or subtract a small number, add, compare, subtract (when the difference is small),
 * divide by phi, and read and write decimals.
 * ====================================================================================== */
#define BIG_WORDS 64                    /* numbers below 2^4096 */
#define BIG_INPUT_WORDS (BIG_WORDS - 4) /* n below 2^3840 (about 10^1156), with room above */
typedef struct { uint64_t w[BIG_WORDS]; } Big;
typedef unsigned __int128 u128;

static Big big_of(uint64_t x) { Big a; memset(&a, 0, sizeof a); a.w[0] = x; return a; }
static void big_inc(Big *a, uint64_t x)  /* a += x */
{
    for (int i = 0; x && i < BIG_WORDS; ++i) { a->w[i] += x; x = a->w[i] < x; }
}
static void big_dec(Big *a, uint64_t x)  /* a -= x */
{
    for (int i = 0; x && i < BIG_WORDS; ++i) { uint64_t borrow = a->w[i] < x; a->w[i] -= x; x = borrow; }
}
static void big_step(Big *a, int64_t x) { if (x >= 0) big_inc(a, (uint64_t)x); else big_dec(a, (uint64_t)-x); }
static void big_add(Big *a, const Big *b)
{
    uint64_t carry = 0;
    for (int i = 0; i < BIG_WORDS; ++i) { u128 s = (u128)a->w[i] + b->w[i] + carry; a->w[i] = (uint64_t)s; carry = (uint64_t)(s >> 64); }
}
static void big_sub(Big *a, const Big *b)
{
    uint64_t borrow = 0;
    for (int i = 0; i < BIG_WORDS; ++i) { u128 d = (u128)a->w[i] - b->w[i] - borrow; a->w[i] = (uint64_t)d; borrow = (uint64_t)(d >> 64) & 1; }
}
static int big_cmp(const Big *a, const Big *b)
{
    for (int i = BIG_WORDS - 1; i >= 0; --i) if (a->w[i] != b->w[i]) return a->w[i] < b->w[i] ? -1 : 1;
    return 0;
}
static int big_words(const Big *a) { int n = BIG_WORDS; while (n && !a->w[n - 1]) --n; return n; }
static int big_below(const Big *a, uint64_t x) { return big_words(a) <= 1 && a->w[0] < x; }
/* a - b, which the caller knows to be small (it stops otherwise). */
static int64_t big_minus(const Big *a, const Big *b)
{
    Big d = *a;
    big_sub(&d, b);
    uint64_t sign = d.w[BIG_WORDS - 1] >> 63 ? ~UINT64_C(0) : 0;
    int small = (d.w[0] >> 63) == (sign & 1);
    for (int i = 1; i < BIG_WORDS; ++i) small &= d.w[i] == sign;
    if (!small) die("far numbers that should be close are not", 0);
    return (int64_t)d.w[0];
}
static int big_mul_small(Big *a, uint64_t x)  /* a *= x; 0 if a no longer fits the input limit */
{
    uint64_t carry = 0;
    for (int i = 0; i < BIG_WORDS; ++i) { u128 p = (u128)a->w[i] * x + carry; a->w[i] = (uint64_t)p; carry = (uint64_t)(p >> 64); }
    return !carry && big_words(a) <= BIG_INPUT_WORDS;
}
static uint64_t big_div_small(Big *a, uint64_t x)  /* a /= x; returns the remainder */
{
    u128 r = 0;
    for (int i = BIG_WORDS - 1; i >= 0; --i) { r = r << 64 | a->w[i]; a->w[i] = (uint64_t)(r / x); r %= x; }
    return (uint64_t)r;
}
/* 12345, 1e100 or 10^100. */
static Big big_parse(const char *s)
{
    Big a = big_of(0);
    const char *p = s;
    int ok = isdigit((unsigned char)*p);
    for (; ok && isdigit((unsigned char)*p); ++p) { ok = big_mul_small(&a, 10); big_inc(&a, (uint64_t)(*p - '0')); }
    if (ok && (*p == 'e' || *p == 'E' || *p == '^')) {
        uint64_t base = 10;
        if (*p == '^') { ok = big_words(&a) <= 1; base = a.w[0]; a = big_of(1); }
        char *end;
        unsigned long e = strtoul(++p, &end, 10);
        ok &= isdigit((unsigned char)*p) && e < 100000;
        for (unsigned long i = 0; ok && i < e; ++i) ok = big_mul_small(&a, base);
        p = end;
    }
    if (!ok || *p) { fprintf(stderr, "spire-at: cannot read %s as a whole number below about 10^1156\n", s); exit(2); }
    return a;
}
static void big_print(Big a, char *out)  /* in decimal */
{
    uint64_t part[BIG_WORDS * 64 / 60 + 2];  /* 19 digits each */
    int n = 0;
    do part[n++] = big_div_small(&a, UINT64_C(10000000000000000000)); while (big_words(&a));
    out += sprintf(out, "%llu", (unsigned long long)part[--n]);
    while (n) out += sprintf(out, "%019llu", (unsigned long long)part[--n]);
}

/* 1/phi = (sqrt 5 - 1) / 2, as INV = floor(2^(64 INV_WORDS) / phi): the integer square root of
 * 5 4^(64 INV_WORDS), found a bit at a time, less 2^(64 INV_WORDS), halved. */
#define INV_WORDS (BIG_WORDS + 2)
static uint64_t inv_phi[INV_WORDS];
static void add_bit(uint64_t *a, int n, int k)  /* a += 2^k, a of n words */
{
    uint64_t add = UINT64_C(1) << (k % 64);
    for (int i = k / 64; add && i < n; ++i) { a[i] += add; add = a[i] < add; }
}
static void compute_inv_phi(void)
{
    enum { S = 2 * INV_WORDS + 1 };
    uint64_t num[S] = {0}, root[S] = {0}, t[S];
    num[2 * INV_WORDS] = 5;
    for (int k = 128 * INV_WORDS + 2; k >= 0; k -= 2) {  /* the root's bits, from the top */
        memcpy(t, root, sizeof t);
        add_bit(t, S, k);                                 /* t = root + 4^(k/2) */
        int ge = 1;
        for (int i = S - 1; i >= 0; --i) if (num[i] != t[i]) { ge = num[i] > t[i]; break; }
        if (ge) {                                         /* num -= t */
            uint64_t borrow = 0;
            for (int i = 0; i < S; ++i) { u128 d = (u128)num[i] - t[i] - borrow; num[i] = (uint64_t)d; borrow = (uint64_t)(d >> 64) & 1; }
        }
        for (int i = 0; i < S; ++i) root[i] = root[i] >> 1 | (i + 1 < S ? root[i + 1] << 63 : 0);
        if (ge) add_bit(root, S, k);
    }
    root[INV_WORDS] -= 1;  /* root was sqrt 5 = 2.236..., now sqrt 5 - 1; halve it */
    for (int i = 0; i < INV_WORDS; ++i) inv_phi[i] = root[i] >> 1 | root[i + 1] << 63;
}
/* x / phi, to within x 2^(-64 INV_WORDS) < 2^-128: its floor and the first 64 bits of its
 * fraction. (Should x / phi lie that close to an integer, the floor and the fraction are off
 * together, and the deviation printed below is still right.) */
static Big big_div_phi(const Big *x, uint64_t *fraction)
{
    int nx = big_words(x);
    uint64_t p[BIG_WORDS + INV_WORDS + 1] = {0};
    for (int i = 0; i < nx; ++i) {
        uint64_t carry = 0;
        for (int j = 0; j < INV_WORDS; ++j) { u128 s = (u128)x->w[i] * inv_phi[j] + p[i + j] + carry; p[i + j] = (uint64_t)s; carry = (uint64_t)(s >> 64); }
        p[i + INV_WORDS] = carry;
    }
    Big q;
    memcpy(q.w, p + INV_WORDS, sizeof q.w);
    if (fraction) *fraction = p[INV_WORDS - 1];
    return q;
}

/* ======================================================================================
 * Copies, however far: each started at a record, reading the copy below it or, at the bottom
 * of the chain, a prefix of sigma made directly.
 * ====================================================================================== */
#define PREFIX (UINT64_C(1) << 16)  /* sigma_30 .. sigma_(30 + PREFIX - 1) */
#define BOTTOM 32768u               /* below this column, a copy's output is read from the prefix */
static uint8_t *prefix;
static uint32_t prefix_U[PREFIX + 1];  /* prefix_U[i] = U(29 + i): the upper columns before sigma_(30+i) */

typedef struct FarCopy FarCopy;
struct FarCopy {
    unsigned cls;       /* its state: a class of the base table */
    uint8_t q[16];      /* symbols it has made and its reader has not taken: q[h .. t) */
    unsigned h, t;
    FarCopy *from;      /* the copy it reads; NULL: its output is the prefix itself */
    uint64_t at;        /* with from == NULL, the index in the prefix of its next symbol */
};
static unsigned far_byte(FarCopy *c);
static unsigned far_symbol(FarCopy *c)  /* the copy's next output symbol */
{
    if (!c->from) { if (c->at >= PREFIX) die("read past the prefix of sigma, at index", c->at); return prefix[c->at++]; }
    if (c->h == c->t) {  /* one step: read a byte, make its 3-12 symbols */
        uint64_t e = entry[c->cls + far_byte(c->from)];
        for (unsigned j = 0; j < LEN(e); ++j) c->q[j] = (uint8_t)symbol(SYMS(e), j);
        c->h = 0; c->t = LEN(e); c->cls = NEXT(e);
    }
    return c->q[c->h++];
}
static unsigned far_byte(FarCopy *c)  /* four symbols */
{
    unsigned b = far_symbol(c);
    for (unsigned i = 1; i < 4; ++i) b |= far_symbol(c) << (2 * i);
    return b;
}
/* The WARM symbols a copy makes next; *U goes from the U before them to the U after them. */
static void far_window(FarCopy *c, uint8_t *win, Big *U)
{
    for (unsigned j = 0; j < WARM; ++j) { win[j] = (uint8_t)far_symbol(c); big_inc(U, win[j] >> 1); }
}
/* A copy's record and counters at input position p, from the WARM input symbols before p and
 * U(p - 1): the paper's identities, as in start_at (spire.c). */
typedef struct { unsigned cls; Big n, m, U; } FarStart;
static FarStart far_record(const uint8_t *win, const Big *p, const Big *Up)
{
    int R = find_record(win);
    if (R < 0 || rec_base[R] < 0) die("no single paused record was left far out; records left:", R < 0 ? 2 : 1);
    FarStart st;
    st.cls = (unsigned)rec_base[R];
    st.m = *p; big_dec(&st.m, rec_Qn[R]);                             /* m = p - |Q| */
    Big Um = *Up;                                                     /* U(m - 1): U(p - 1) less */
    for (unsigned i = 0; i < rec_Qn[R]; ++i) big_dec(&Um, win[WARM - rec_Qn[R] + i] >> 1);  /* m .. p-1 */
    st.n = st.m; big_add(&st.n, &Um); big_step(&st.n, rec_z[R]);      /* n = m + U(m - 1) + z */
    st.U = st.m; big_step(&st.U, rec_w[R] - rec_Dn[R]);               /* U(n - 1) = m + w - |D| */
    return st;
}
/* Start copy c at input position p, reading `from` (whose next symbol is sigma_(p - WARM), and
 * *U = U(p - WARM - 1)), and walk it to column col: its next symbol is then sigma_col, and *U
 * is U(col - 1). */
static void far_start(FarCopy *c, FarCopy *from, Big *U, const Big *p, const Big *col)
{
    uint8_t win[WARM];
    far_window(from, win, U);
    FarStart st = far_record(win, p, U);
    int64_t walk = big_minus(col, &st.n);
    if (walk < 0) die("a far copy started past its column, by", (uint64_t)-walk);
    c->cls = st.cls; c->from = from; c->h = c->t = 0;
    *U = st.U;
    for (int64_t i = 0; i < walk; ++i) big_inc(U, far_symbol(c) >> 1);
}
/* The top copy, at column col with counters m and n + U = nu, reading `in`, walked on to column
 * n: the row there, m or nu plus the row's offset (as walk_block in spire.c). */
static Big far_walk_to(unsigned cls, FarCopy *in, const Big *col, Big m, Big nu, const Big *n)
{
    int64_t d = big_minus(n, col);
    if (d < 0) die("the top copy started past column n, by", (uint64_t)-d);
    for (uint64_t at = 0;;) {
        uint64_t e = entry[cls + far_byte(in)];
        if (at + LEN(e) > (uint64_t)d) {
            unsigned code = CODES(e)[d - at];
            Big q = code >> 7 ? nu : m;
            big_inc(&q, code & 127);
            return q;
        }
        at += LEN(e); big_inc(&m, DM(e)); big_inc(&nu, LEN(e) + DU(e)); cls = NEXT(e);
    }
}
/* Where a copy that must reach column c finds its record: input_start (spire.c), for Big. */
static Big far_input_start(const Big *c)
{
    Big x = *c;
    big_dec(&x, 48 + MARGIN);
    x = big_div_phi(&x, NULL);
    x.w[0] &= ~UINT64_C(3);
    big_inc(&x, 30);
    return x;
}

/* q_n, with the chain aimed `lead` columns before n (normally 0; the top copy walks the rest). */
static Big far_row(const Big *n, uint64_t lead)
{
    const uint8_t *first = qf_packets + QF_INITIAL_PACKET;
    if (big_below(n, 48)) {  /* the seed's rows, as in run_start (spire.c) */
        uint64_t c = n->w[0];
        return big_of(c < 30 ? qf_seed_queens[c] : (first[3 + c - 30] >> 7 ? 30 + QF_INITIAL_UPPER : QF_INITIAL_M) + (first[3 + c - 30] & 127));
    }
    Big aim = *n, lead_big = big_of(lead);
    int from_seed = big_cmp(n, &lead_big) <= 0;
    if (!from_seed) { big_sub(&aim, &lead_big); from_seed = big_below(&aim, BOTTOM); }
    if (from_seed) {  /* near the start: the top copy from the seed, reading sigma_30 on */
        FarCopy in = {0};
        Big col = big_of(48), m = big_of(QF_INITIAL_M + first[1]), nu = big_of(48 + QF_INITIAL_UPPER + first[2]);
        return far_walk_to(QF_INITIAL_STATE, &in, &col, m, nu, n);
    }
    /* The chain, from the top down: copy k finds its record at p[k] and must reach column
     * p[k-1] - WARM (copy 0, the top, column aim), until a column is below BOTTOM. */
    int levels = 0, room = 64;
    Big *p = (Big *)malloc(room * sizeof(Big)), c = aim;
    while (!big_below(&c, BOTTOM)) {
        if (levels == room) p = (Big *)realloc(p, (room *= 2) * sizeof(Big));
        p[levels] = far_input_start(&c);
        c = p[levels++]; big_dec(&c, WARM);
    }
    /* From the bottom up: the prefix at column c, then each copy started from the one below. */
    FarCopy *copy = (FarCopy *)calloc(levels + 1, sizeof(FarCopy));
    copy[levels].at = c.w[0] - 30;
    Big U = big_of(prefix_U[c.w[0] - 30]);
    for (int k = levels - 1; k >= 1; --k) {
        Big col = p[k - 1];
        big_dec(&col, WARM);
        far_start(&copy[k], &copy[k + 1], &U, &p[k], &col);
    }
    /* The top copy: its record at p[0], reading copy 1; then on to column n. */
    uint8_t win[WARM];
    far_window(&copy[1], win, &U);
    FarStart st = far_record(win, &p[0], &U);
    Big nu = st.n;
    big_add(&nu, &st.U);
    Big q = far_walk_to(st.cls, &copy[1], &st.n, st.m, nu, n);
    free(copy); free(p);
    return q;
}

/* ======================================================================================
 * main: the rows on all threads (they are independent), printed in order.
 * ====================================================================================== */
typedef struct { int count, room; Big *n; } Columns;
static void add_column(Columns *c, const char *s)
{
    if (c->count == c->room) c->n = (Big *)realloc(c->n, (c->room = c->room ? 2 * c->room : 64) * sizeof(Big));
    c->n[c->count++] = big_parse(s);
}
int main(int argc, char **argv)
{
    Columns cols = {0};
    uint64_t lead = 0;
    char word[4096];
    for (int i = 1; i < argc; ++i) {
        if (!strcmp(argv[i], "--walk") && i + 1 < argc) lead = parse_count(argv[++i]);
        else if (strcmp(argv[i], "-")) add_column(&cols, argv[i]);
        else while (scanf("%4095s", word) == 1) add_column(&cols, word);
    }
    if (!cols.count) {
        fprintf(stderr, "usage: spire-at [--walk D] n [n ...]   or   spire-at -   (the n from standard input)\n"
                        "  q_n for each n (up to about 10^1150), and its deviation from n phi or n / phi\n");
        return 2;
    }
    double t0 = now();
    widen_entries();
    for (unsigned x = 1; x < 30; ++x) U29 += qf_seed_queens[x] > x;
    prefix = make_sigma(PREFIX);
    prefix_U[0] = U29;
    for (uint64_t i = 0; i < PREFIX; ++i) prefix_U[i + 1] = prefix_U[i] + (prefix[i] >> 1);
    compute_inv_phi();
    double t1 = now();

    Big *q = (Big *)malloc(cols.count * sizeof(Big));
    double *secs = (double *)malloc(cols.count * sizeof(double));
#pragma omp parallel for schedule(dynamic, 1)
    for (int i = 0; i < cols.count; ++i) {
        double t = now();
        q[i] = far_row(&cols.n[i], lead);
        secs[i] = now() - t;
    }
    static char n_text[BIG_WORDS * 20 + 2], q_text[BIG_WORDS * 20 + 2];
    for (int i = 0; i < cols.count; ++i) {
        /* q_n = n phi + O(1) for an upper queen (above the diagonal), else n / phi + O(1) (the
         * paper's theorem). The deviation is q_n less the one it follows; as n phi = n + n / phi,
         * either is an integer part and the fraction of n / phi. */
        const Big *n = &cols.n[i];
        int upper = big_cmp(&q[i], n) > 0;
        uint64_t fraction;
        Big whole = big_div_phi(n, &fraction);
        if (upper) big_add(&whole, n);
        double deviation = (double)big_minus(&q[i], &whole) - (double)fraction * 0x1p-64;
        big_print(*n, n_text); big_print(q[i], q_text);
        printf("{\"n\":%s,\"q\":%s,\"near\":\"%s\",\"deviation\":%.6f,\"seconds\":%.6f}\n",
               n_text, q_text, upper ? "n*phi" : "n/phi", deviation, secs[i]);
    }
    fprintf(stderr, "{\"rows\":%d,\"threads\":%d,\"setup\":%.3f,\"seconds\":%.3f,\"peak_mib\":%.1f}\n",
            cols.count, omp_get_max_threads(), t1 - t0, now() - t0, peak_memory() / 1048576);
    return 0;
}
