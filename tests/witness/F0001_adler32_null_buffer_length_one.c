/* Witness for ledger entry F0001.

   The zlib manual says of adler32(): "If buf is Z_NULL, this function
   returns the required initial value for the checksum."  This program
   checks that promise at several lengths, including 1.

   It exits with status 0 if every call returns 1.  On unpatched zlib 1.4
   the call with length 1 dereferences a null pointer, so the program does
   not exit normally. */

#include "zlib.h"

int main(void) {
    static const unsigned lengths[] = {0, 1, 2, 15, 16, 5552};
    unsigned i;

    for (i = 0; i < sizeof(lengths) / sizeof(lengths[0]); i++) {
        if (adler32(0L, Z_NULL, (uInt)lengths[i]) != 1L)
            return 1;
        if (adler32_z(0L, Z_NULL, (z_size_t)lengths[i]) != 1L)
            return 1;
    }
    return 0;
}
