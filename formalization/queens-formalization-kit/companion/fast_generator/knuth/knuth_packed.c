/* Derived by knuth/derive_knuth_packed.py from Knuth's infty-queens.w:
 * its array allocation and queen placement, with the occupancy flags stored
 * as bits in 64-bit words and 64-bit counts and indices, in a program that
 * generates and checksums the rows like build/queens_fast.
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
#define slack 10
#define phi 1.6180339887498948482
#define o ((void)0)
int64_t goal;
uint64_t *a, *b, *c;
int64_t maxmema, maxmemb, minmemc, maxmemc;
uint64_t a_bits, b_bits, c_bits;

/* Each occupancy flag occupies one bit in a 64-bit unsigned word. */
static uint64_t packed_bytes(uint64_t bits) {
    return ((bits + 63) / 64) * sizeof(uint64_t);
}
static unsigned get_bit(const uint64_t *bits, uint64_t index) {
    return (unsigned)((bits[index >> 6] >> (index & 63)) & UINT64_C(1));
}
static void set_bit(uint64_t *bits, uint64_t index) {
    bits[index >> 6] |= UINT64_C(1) << (index & 63);
}
/* The assert-enabled build also checks the reads, which Knuth leaves unchecked. */
#define GET(array, index) \
    (assert((index) >= 0 && (uint64_t)(index) < array##_bits), \
     get_bit(array, (uint64_t)(index)))
#define SET(array, index) \
    (assert((index) >= 0 && (uint64_t)(index) < array##_bits), \
     set_bit(array, (uint64_t)(index)))


int main(int argc, char **argv) {
    int emit = 0;
    uint64_t count = 0, hash = UINT64_C(14695981039346656037);
    uint64_t computed = 0, last_row = 0;
    int64_t k, n, q, r, s, t;
    clock_t started;
    for (int arg = 1; arg < argc; ++arg) {
        if (!strcmp(argv[arg], "--emit")) emit = 1;
        else if (!strcmp(argv[arg], "--count") && arg + 1 < argc) {
            char *end;
            errno = 0;
            const char *value = argv[++arg];
            if (*value == '-') return 2;
            count = strtoull(value, &end, 10);
            if (errno || *end || end == value) return 2;
        } else {
            fprintf(stderr, "Usage: %s --count N [--emit]\n", argv[0]);
            return 2;
        }
    }
    /* Limit this adapter to its intended benchmark range. All placement
       arithmetic and allocation sizes use 64-bit types; signed indices
       are needed for k-n and Knuth's diagonal-offset tests. */
    if (sizeof(size_t) < 8 || !count || count > UINT64_C(1000000000000)) {
        fprintf(stderr, "requires 64-bit size_t and count in [1, 1000000000000]\n");
        return 2;
    }
    goal = (int64_t)count;
    started = clock();

#line 83 "infty-queens.w"

maxmema= ((int64_t)(phi*goal)+slack);
maxmemb= (maxmema+goal);
maxmemc= (maxmema-goal);
minmemc= (goal-maxmemc+2*slack);
a_bits= (uint64_t)(maxmema);
a= (uint64_t*)calloc((size_t)((a_bits+63)/64),sizeof(uint64_t));
if(!a){
fprintf(stderr,"Can't allocate array a!\n");
exit(-2);
}
b_bits= (uint64_t)(maxmemb);
b= (uint64_t*)calloc((size_t)((b_bits+63)/64),sizeof(uint64_t));
if(!b){
fprintf(stderr,"Can't allocate array b!\n");
exit(-2);
}
c_bits= (uint64_t)(minmemc+maxmemc);
c= (uint64_t*)calloc((size_t)((c_bits+63)/64),sizeof(uint64_t));
if(!c){
fprintf(stderr,"Can't allocate array c!\n");
exit(-2);
}


    r = t = 0; s = 1;
    for (n = 1; n <= goal; ++n) {

#line 108 "infty-queens.w"

for(k= s;k<=n-r;k++){
if(k+n>=maxmemb)goto done;
if(o,GET(b, k+n)==0){
if(k-n+minmemc<0)goto done;
if(o,GET(c, k-n+minmemc)==0){
if(o,GET(a, k)==0){
q= k;
o,SET(a, k);
if(k==s)
for(s= k+1;o,GET(a, s)==1;s++);
o,SET(b, k+n);
o,SET(c, k-n+minmemc);
if(k-n==-r)
for(r= n-k+1;;r++){
if(r> minmemc)goto done;
if(o,GET(c, minmemc-r)==0)break;
}
goto got_q;
}
}
}
}
t++;
if(t>=maxmemc)goto done;
o,SET(c, t+minmemc);
q= n+t;
if(q>=maxmema)goto done;
o,SET(a, q);
if(q+n>=maxmemb)goto done;
o,SET(b, q+n);
got_q:


        ; /* The extracted chunk ends with label got_q. */
        last_row = (uint64_t)(q - 1);
        hash = (hash ^ last_row) * UINT64_C(1099511628211);
        ++computed;
        if (emit) printf("%" PRId64 " %" PRIu64 "\n", n - 1, last_row);
    }
done:
    {
        double seconds = (double)(clock() - started) / CLOCKS_PER_SEC;
        uint64_t bytes = packed_bytes(a_bits) + packed_bytes(b_bits)
                       + packed_bytes(c_bits);
        FILE *summary = emit ? stderr : stdout;
        if (computed != count) {
            fprintf(stderr, "Knuth allocation was exhausted after %" PRIu64
                    " queens (requested %" PRIu64 ")\n", computed, count);
            free(a); free(b); free(c);
            return 3;
        }
        fprintf(summary,
                "{\"algorithm\":\"knuth-packed\",\"count\":%" PRIu64 ",\"last_column\":%" PRIu64
                ",\"last_queen\":%" PRIu64 ",\"hash\":\"%016" PRIx64
                "\",\"requested_array_bytes\":%" PRIu64
                ",\"algorithm_bytes\":%" PRIu64 ",\"seconds\":%.9f}\n",
                count, count - 1, last_row, hash, bytes, bytes, seconds);
        free(a); free(b); free(c);
    }
    return 0;
}
