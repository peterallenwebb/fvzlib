# How zlib sources are given to the verifier.
#
# ZLIB_DEFINES are the preprocessor flags clightgen receives for every zlib
# source file.  They stand for what the upstream ./configure establishes on
# the project's first target, x86-64 Linux.  ZLIB_VERIFIED lists the source
# files that have proofs.
#
# Do not change these by hand to make a proof go through.
# tools/check_build.py runs the real ./configure and compares, token by
# token, what the upstream build compiles with what these flags give the
# verifier.

ZLIB_DEFINES  := -DHAVE_UNISTD_H -DHAVE_STDARG_H -DHAVE_HIDDEN -D_LARGEFILE64_SOURCE=1
ZLIB_VERIFIED := adler32.c
