# Build and check the fvzlib specifications.
#
#   make          compile the Rocq sources, which also runs the test vectors
#   make check    compile, then run the layer, assumption, trace, patch,
#                 and precondition review checks
#   make full     everything: the toolchain and target check, `make check`,
#                 the check that the verified source is the built source,
#                 the differential test of the reference model against
#                 zlib, and every proof.  Run it inside the pinned switch:
#                   opam exec --switch=fvzlib -- make full
#                 It fails anywhere but the project's first target, x86-64
#                 Linux.  Elsewhere use `make full EXPLORATORY=1`.
#   make mutants  mutation testing: change adler32.c in several hundred
#                 small ways and check that a proof fails for each.  Needs
#                 `make check` and `make proofs` first.  Took 24 and 50
#                 minutes in two runs on sixteen processors, so
#                 `make full` does not run it.
#                 JOBS sets how many mutants are checked at once.
#   make clean    remove build products
#
# tools/bootstrap.sh installs the pinned toolchain.
#
# UPSTREAM is the pinned upstream zlib tree.  It is a git submodule, so run
# `git submodule update --init` once after cloning.

ROCQ_MAKEFILE := Makefile.rocq
UPSTREAM ?= upstream/zlib

.PHONY: all check clean full env-check build-check differential proofs \
        spikes mutants

all: $(ROCQ_MAKEFILE)
	$(MAKE) -f $(ROCQ_MAKEFILE)

$(ROCQ_MAKEFILE): _CoqProject
	rocq makefile -f _CoqProject -o $(ROCQ_MAKEFILE)

check: all
	python3 tools/check_layers.py
	python3 tools/check_assumptions.py
	python3 tools/check_trace.py --upstream $(UPSTREAM) --strict
	python3 tools/check_patches.py --upstream $(UPSTREAM)
	python3 tools/check_preconditions.py

env-check:
	python3 tools/check_env.py $(if $(EXPLORATORY),--exploratory)

build-check:
	python3 tools/check_build.py

differential:
	python3 -B tools/check_differential.py

proofs:
	$(MAKE) -C proofs/lib
	$(MAKE) -C proofs/adler32

spikes:
	$(MAKE) -C spikes/transfer
	$(MAKE) -C spikes/termination

mutants:
	python3 -B tools/check_mutants.py $(if $(JOBS),--jobs $(JOBS))

# In this order: a wrong toolchain stops the run at once, and `check` makes
# the patched tree that the later steps read.
full:
	$(MAKE) env-check
	$(MAKE) check
	$(MAKE) build-check
	$(MAKE) differential
	$(MAKE) proofs
	$(MAKE) spikes
	@echo "full: all checks passed$(if $(EXPLORATORY), on an exploratory target)"

clean:
	$(MAKE) -C proofs/lib clean
	$(MAKE) -C proofs/adler32 clean
	$(MAKE) -C spikes/transfer clean
	$(MAKE) -C spikes/termination clean
	if [ -f $(ROCQ_MAKEFILE) ]; then $(MAKE) -f $(ROCQ_MAKEFILE) cleanall; fi
	rm -f $(ROCQ_MAKEFILE) $(ROCQ_MAKEFILE).conf
	rm -rf build
