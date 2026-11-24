# Build and check the fvzlib specifications.
#
#   make          compile the Rocq sources, which also runs the test vectors
#   make check    compile, then run the layer, assumption, trace, and patch
#                 checks
#   make clean    remove build products
#
# UPSTREAM is the pinned upstream zlib tree.  It is a git submodule, so run
# `git submodule update --init` once after cloning.

ROCQ_MAKEFILE := Makefile.rocq
UPSTREAM ?= upstream/zlib

.PHONY: all check clean

all: $(ROCQ_MAKEFILE)
	$(MAKE) -f $(ROCQ_MAKEFILE)

$(ROCQ_MAKEFILE): _CoqProject
	rocq makefile -f _CoqProject -o $(ROCQ_MAKEFILE)

check: all
	python3 tools/check_layers.py
	python3 tools/check_assumptions.py
	python3 tools/check_trace.py --upstream $(UPSTREAM) --strict
	python3 tools/check_patches.py --upstream $(UPSTREAM)

clean:
	if [ -f $(ROCQ_MAKEFILE) ]; then $(MAKE) -f $(ROCQ_MAKEFILE) cleanall; fi
	rm -f $(ROCQ_MAKEFILE) $(ROCQ_MAKEFILE).conf
	rm -rf build
