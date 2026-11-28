/* A whole program that calls every function of adler32.c.

   This file is ours, not zlib's.  VST's soundness theorem speaks of a
   whole program with a main function, and a library has none.  This
   program is the smallest one that reaches all five functions of
   adler32.c: main calls the four public ones, and two of those call the
   internal one.

   adler32.c is included, not linked, so that the translation gives one
   Clight program.  Client.v checks that each of the five functions comes
   out exactly as it does when adler32.c is translated alone.

   The calls: a null buffer, a whole buffer, the same buffer in two
   pieces, and the two checksums of the pieces combined. */

#include "adler32.c"

int main(void) {
    unsigned char data[9];
    uLong start, whole, again, first, second, both, wide;

    data[0] = 'W';
    data[1] = 'i';
    data[2] = 'k';
    data[3] = 'i';
    data[4] = 'p';
    data[5] = 'e';
    data[6] = 'd';
    data[7] = 'i';
    data[8] = 'a';

    start = adler32(0L, Z_NULL, 0);
    whole = adler32(start, data, 9);
    again = adler32_z(start, data, 9);
    first = adler32(start, data, 4);
    second = adler32(start, data + 4, 5);
    both = adler32_combine(first, second, 5);
    wide = adler32_combine64(first, second, 5);
    return 0;
}
