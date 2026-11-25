# F0001: adler32 with a null buffer and length 1 dereferences the null pointer

| Field | Value |
|---|---|
| Status | Resolved in the patch sequence by a hardening patch. Not submitted upstream. |
| Found | 2026-11-24, while writing the Layer 2 specification |
| Release | zlib 1.4, commit `99623ef7097352da7993ba614161fd6a311e046e` |
| File | `adler32.c`, function `adler32_z`, reached from `adler32` |
| C editions affected | All. A null pointer dereference is undefined in every edition. |
| Patch | `patches/0001-adler32-null-buffer-before-one-byte-path.patch` |
| Witness | `tests/witness/F0001_adler32_null_buffer_length_one.c` |

## What the manual says

`zlib.h`, entry for `adler32`:

> If buf is Z_NULL, this function returns the required initial value for the
> checksum.

The sentence places no condition on `len`.

## What the code does

`adler32_z` handles a length of 1 before it tests for a null buffer:

```c
    /* in case user likes doing a byte at a time, keep it fast */
    if (len == 1) {
        adler += buf[0];
        ...
        return adler | (sum2 << 16);
    }

    /* initial Adler-32 value (deferred check for len == 1 speed) */
    if (buf == Z_NULL)
        return 1L;
```

So a call with `buf == Z_NULL` and `len == 1` reads `buf[0]`. The comment
shows the order is deliberate.

## Witness

```c
#include <stdio.h>
#include "zlib.h"
int main(int argc, char **argv) {
    unsigned len = (unsigned)(argc > 1 ? argv[1][0] - '0' : 0);
    printf("adler32(1, Z_NULL, %u) = ", len); fflush(stdout);
    printf("%lu\n", adler32(1L, Z_NULL, len));
    return 0;
}
```

Built against `adler32.c` from the release above, with Apple clang 17 on
ARM macOS, at both `-O0` and `-O2`:

| `len` | Result |
|---|---|
| 0 | Prints 1 |
| 2 | Prints 1 |
| 1 | Killed by a segmentation fault, exit status 139 |

This witness was run on the development machine. The build's own witness,
which makes the call with a length of 1, was repeated on the x86-64 Linux
target on 2026-11-25. See Resolution below.

## Assessment

- The usage example in the manual calls `adler32(0L, Z_NULL, 0)`, and that
  call works. A caller has to pass a null buffer together with a length of
  exactly 1 to reach the fault.
- The Layer 2 specification follows the manual and promises the initial
  value for a null buffer whatever the length. The C contract in Layer 3
  therefore cannot be proven for unpatched zlib 1.4 as the manual stands.
- Security impact looks low, since the fault needs a caller that passes a
  null buffer with a non-zero length. That judgment is ours and has not been
  reviewed.

## Resolution

Decided 2026-11-24: a hardening patch. The null test moves in front of the
one-byte path, so the code keeps the manual's promise at every length. The
manual is left as it is, and so is the Layer 2 specification.

The patch changes behavior for one call only, a null buffer with a length of
1, which was undefined and now returns 1. For every other call the same
statements run in the same order as before. The patch header gives the
argument in full.

The build applies the patch and runs the witness against both trees. The
witness must fail on pristine zlib and pass on the patched tree. On the
development machine it is killed by signal 11 on the pristine tree and exits
with status 0 on the patched one. On the x86-64 Linux target, built with gcc
15.2, the result is the same.

## Cost

The one-byte path executes one more comparison. Measured on the development
machine, an ARM Mac with Apple clang 17 at `-O3`, best of five runs:

| Workload | Pristine | Patched |
|---|---|---|
| 300 million calls of one byte each | 0.868 s | 0.863 s |
| 4096 bytes per call, same total work for both | 0.789 s | 0.791 s |

The difference is within the noise of the measurement, and both builds
return identical checksums. This must be repeated on the x86-64 Linux
target, with gcc as well as clang, before the patch is offered upstream.

## Alternatives not taken

1. **Documentation patch.** State in the manual that `len` must not be 1
   when `buf` is `Z_NULL`. This would weaken a promise that callers may
   already rely on.
2. **Both.** Not needed once the code keeps the promise.
