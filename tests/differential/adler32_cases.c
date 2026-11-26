/* adler32_cases.c -- run zlib's Adler-32 functions and print what they return
 *
 * Part of the differential test of the Adler-32 reference model.  See
 * tools/check_differential.py, which builds this program against a zlib
 * library, and tests/differential/Adler32Harness.v, which holds the Rocq
 * side.
 *
 * The program makes several thousand calls to adler32, adler32_z,
 * adler32_combine, and adler32_combine64, and prints one line for each
 * case: the input and the value zlib returned.  It prints nothing about
 * what the value should be.  That is for the model to say.
 *
 * The inputs come from a fixed pseudo-random sequence, so every run prints
 * the same lines.
 *
 * Each input is copied into a block of memory of exactly its own length
 * before the call, so that a build with an address checker sees any read
 * outside the buffer.
 *
 * Not called: adler32 with a null buffer and a length of 1.  Pristine
 * zlib 1.4 reads through the null pointer there.  That is finding F0001,
 * and tests/witness covers it.
 *
 * Line formats, where DATA is "hex:" and hexadecimal digits, or
 * "run:COUNT:FIRST:STEP" for the bytes FIRST, FIRST+STEP, ... mod 256:
 *
 *   initial RESULT                      a call with a null buffer
 *   whole DATA RESULT                   one call from the initial value
 *   prose DATA RESULT                   the same, on a short input
 *   pieces RESULT DATA...               one call per DATA, chained
 *   vector NAME RESULT DATA...          the same, for a named test vector
 *   combine A1 A2 LEN2 RESULT           one call to a combine function
 *   joined DATA DATA A1 A2 RESULT       two checksums and their combination
 */

#define _LARGEFILE64_SOURCE 1
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include <stdint.h>
#include "zlib.h"

/* ---- a fixed pseudo-random sequence (splitmix64) ---- */

static uint64_t state = 0x66767a6c6962ULL;      /* "fvzlib" */

static uint64_t next(void) {
    uint64_t z = (state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

static uint64_t below(uint64_t n) { return next() % n; }

/* ---- inputs ---- */

typedef struct {
    size_t len;
    unsigned char *bytes;       /* the input, for printing */
    int is_run;                 /* described by count, first, step */
    unsigned first, step;
} data;

static void *must(void *p) {
    if (p == NULL) { fprintf(stderr, "out of memory\n"); exit(2); }
    return p;
}

/* Random bytes.  Three kinds: any byte, high bytes only, which drive the
   sums up fastest, and mostly zero. */
static data random_data(size_t len) {
    data d = { len, must(malloc(len ? len : 1)), 0, 0, 0 };
    unsigned kind = (unsigned)below(4);
    for (size_t i = 0; i < len; i++) {
        unsigned b = (unsigned)below(256);
        if (kind == 2) b |= 0xf0;
        if (kind == 3 && below(8)) b = 0;
        d.bytes[i] = (unsigned char)b;
    }
    return d;
}

static data run_data(size_t len, unsigned first, unsigned step) {
    data d = { len, must(malloc(len ? len : 1)), 1, first, step };
    for (size_t i = 0; i < len; i++)
        d.bytes[i] = (unsigned char)(first + i * step);
    return d;
}

static data text_data(const char *text) {
    data d = { strlen(text), must(malloc(strlen(text) + 1)), 0, 0, 0 };
    memcpy(d.bytes, text, d.len);
    return d;
}

static void print_data(const data *d) {
    if (d->is_run) {
        printf(" run:%zu:%u:%u", d->len, d->first, d->step);
        return;
    }
    printf(" hex:");
    for (size_t i = 0; i < d->len; i++)
        printf("%02x", d->bytes[i]);
}

static void release(data *d) { free(d->bytes); d->bytes = NULL; }

/* ---- calls ---- */

static unsigned long calls = 0;

/* One call on a copy of the input that is exactly as long as the input.
   An empty input gets a block of one byte, since the manual does not say
   that a buffer of length zero may be anything but a real pointer.
   `which` picks adler32 or adler32_z. */
static uLong call(uLong adler, const data *d, int which) {
    unsigned char *exact = must(malloc(d->len ? d->len : 1));
    uLong result;
    if (d->len) memcpy(exact, d->bytes, d->len);
    if (which && d->len <= UINT_MAX)
        result = adler32(adler, exact, (uInt)d->len);
    else
        result = adler32_z(adler, exact, d->len);
    free(exact);
    calls++;
    return result;
}

static uLong initial_value;

static void whole(const char *kind, data d) {
    uLong result = call(initial_value, &d, (int)below(2));
    printf("%s", kind);
    print_data(&d);
    printf(" %lu\n", result);
    release(&d);
}

static void pieces(const char *label, data *ds, int count) {
    uLong adler = initial_value;
    for (int i = 0; i < count; i++)
        adler = call(adler, &ds[i], (int)below(2));
    printf("%s %lu", label, adler);
    for (int i = 0; i < count; i++) {
        print_data(&ds[i]);
        release(&ds[i]);
    }
    printf("\n");
}

static void vector(const char *name, data d) {
    char label[80];
    snprintf(label, sizeof label, "vector %s", name);
    pieces(label, &d, 1);
}

static size_t piece_length(void) {
    switch (below(6)) {
    case 0: return 0;
    case 1: return 1;
    case 2: return (size_t)below(16);
    case 3: return (size_t)below(200);
    case 4: return 16 * (size_t)below(40);
    default: return (size_t)below(7000);
    }
}

/* A value with the form of a checksum: both halves below 65521. */
static uLong checksum_form(void) {
    static const unsigned long edge[] = { 0, 1, 2, 65519, 65520 };
    unsigned long low = below(3) ? below(65521) : edge[below(5)];
    unsigned long high = below(3) ? below(65521) : edge[below(5)];
    return (high << 16) | low;
}

static void combine(uLong a1, uLong a2, long long len2) {
    printf("combine %lu %lu %lld %lu\n", a1, a2, len2,
           adler32_combine(a1, a2, (z_off_t)len2));
    printf("combine %lu %lu %lld %lu\n", a1, a2, len2,
           adler32_combine64(a1, a2, (z_off64_t)len2));
    calls += 2;
}

int main(void) {
    static const size_t edges[] = {
        5551, 5552, 5553, 5567, 5568, 5569, 11103, 11104, 11105, 16656,
        16657, 22208, 65535, 65536 };
    static const size_t run_lengths[] = {
        1, 2, 15, 16, 17, 255, 256, 5551, 5552, 5553, 11104 };
    static const unsigned run_kinds[][2] = {
        { 255, 0 }, { 0, 0 }, { 0, 1 }, { 128, 7 }, { 255, 255 } };
    static const long long lengths[] = {
        0, 1, 2, 65520, 65521, 65522, 131042, 2147483647LL, 2147483648LL,
        4294967295LL, 4294967296LL, 4294967297LL, 4611686018427387904LL,
        9223372036854775807LL };

    /* ---- the initial value: a null buffer ---- */
    initial_value = adler32(0L, Z_NULL, 0);
    printf("initial %lu\n", initial_value);
    {
        static const uLong seeds[] = { 0, 1, 65521, 0xffffffffUL,
                                       0xfff1fff1UL, 0x12345678UL };
        static const uInt counts[] = { 0, 2, 15, 16, 5552, UINT_MAX };
        for (int i = 0; i < 6; i++)
            for (int j = 0; j < 6; j++) {
                printf("initial %lu\n", adler32(seeds[i], Z_NULL, counts[j]));
                printf("initial %lu\n", adler32_z(seeds[i], Z_NULL,
                       j == 5 ? SIZE_MAX : (z_size_t)counts[j]));
                calls += 2;
            }
    }

    /* ---- the test vectors of spec/format/Adler32Tests.v ---- */
    vector("prose_empty", text_data(""));
    vector("prose_a", text_data("a"));
    vector("prose_abc", text_data("abc"));
    vector("prose_message_digest", text_data("message digest"));
    vector("prose_alphabet", text_data("abcdefghijklmnopqrstuvwxyz"));
    vector("prose_wikipedia", text_data("Wikipedia"));
    vector("code_alphabet", text_data("abcdefghijklmnopqrstuvwxyz"));
    vector("code_ff_5553", run_data(5553, 255, 0));
    vector("code_all_bytes_x4", run_data(1024, 0, 1));
    vector("code_zeros_1000", run_data(1000, 0, 0));
    {
        data two[2] = { text_data("message "), text_data("digest") };
        pieces("vector code_two_pieces", two, 2);
    }

    /* ---- one call: short inputs, also for the prose definition ---- */
    for (size_t len = 0; len <= 64; len++)
        for (int i = 0; i < 4; i++)
            whole("prose", random_data(len));

    /* ---- one call: every length up to 400, twice ---- */
    for (size_t len = 0; len <= 400; len++)
        for (int i = 0; i < 2; i++)
            whole("whole", random_data(len));

    /* ---- one call: lengths around the block sizes, and random ones ---- */
    for (size_t i = 0; i < sizeof edges / sizeof edges[0]; i++)
        whole("whole", random_data(edges[i]));
    for (int i = 0; i < 30; i++)
        whole("whole", random_data((size_t)below(20000)));

    /* ---- one call: long regular inputs ---- */
    for (size_t i = 0; i < sizeof run_lengths / sizeof run_lengths[0]; i++)
        for (size_t k = 0; k < sizeof run_kinds / sizeof run_kinds[0]; k++)
            whole("whole", run_data(run_lengths[i], run_kinds[k][0],
                                    run_kinds[k][1]));
    whole("whole", run_data(65521, 255, 0));
    whole("whole", run_data(65536, 0, 1));
    whole("whole", run_data(200000, 255, 0));

    /* ---- several calls, chained ---- */
    for (int i = 0; i < 120; i++) {
        data ds[12];
        int count = 1 + (int)below(12);
        for (int k = 0; k < count; k++)
            ds[k] = random_data(piece_length());
        pieces("pieces", ds, count);
    }
    /* one byte at a time, the path the code keeps fast */
    for (int i = 0; i < 20; i++) {
        data ds[12];
        for (int k = 0; k < 12; k++)
            ds[k] = run_data(1, 240 + (unsigned)below(16), 0);
        pieces("pieces", ds, 12);
    }

    /* ---- combining: values with the form of a checksum, any length ---- */
    /* C does not fix the order in which arguments are evaluated, so each
       random value is drawn in a statement of its own. */
    for (size_t i = 0; i < sizeof lengths / sizeof lengths[0]; i++)
        for (int k = 0; k < 20; k++) {
            uLong a1 = checksum_form();
            uLong a2 = checksum_form();
            combine(a1, a2, lengths[i]);
        }
    for (int i = 0; i < 1500; i++) {
        uLong a1 = checksum_form();
        uLong a2 = checksum_form();
        uint64_t bits = next();
        unsigned shift = 1 + (unsigned)below(63);
        combine(a1, a2, (long long)(bits >> shift));
    }

    /* ---- combining: the checksums of two real inputs ---- */
    for (int i = 0; i < 150; i++) {
        data d1 = random_data(piece_length());
        data d2 = random_data(piece_length());
        uLong a1 = call(initial_value, &d1, (int)below(2));
        uLong a2 = call(initial_value, &d2, (int)below(2));
        uLong joined = below(2) ? adler32_combine(a1, a2, (z_off_t)d2.len)
                                : adler32_combine64(a1, a2, (z_off64_t)d2.len);
        calls++;
        printf("joined");
        print_data(&d1);
        print_data(&d2);
        printf(" %lu %lu %lu\n", a1, a2, joined);
        release(&d1);
        release(&d2);
    }

    fprintf(stderr, "%lu calls to zlib\n", calls);
    return 0;
}
