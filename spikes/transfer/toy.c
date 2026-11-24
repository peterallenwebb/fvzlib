/* Toy function for the contract transfer spike.

   It has the two features the spike is about: a loop, and a forward goto
   out of that loop to a cleanup label at the end of the function.  The
   cleanup code writes to memory and returns, like the epilogue of zlib's
   inflate.

   count_down counts n down to zero, or down to `stop` if it meets that
   value first.  It stores the number of steps taken in *out and returns
   the value at which it stopped. */

unsigned count_down(unsigned n, unsigned stop, unsigned *out) {
    unsigned steps = 0;

    while (n != 0) {
        if (n == stop)
            goto leave;
        n--;
        steps++;
    }
  leave:
    *out = steps;
    return n;
}
