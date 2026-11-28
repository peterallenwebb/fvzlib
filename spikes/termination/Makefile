# Termination spike.  Needs the pinned toolchain, including VST, and the
# main proofs built: run `make proofs` at the top of the repository first.
#
#   make        check the one file left here
#   make clean  remove build products
#
# What this spike began is now in proofs/adler32 and proofs/lib.  One
# experiment remains, which is exploratory and not part of `make check`.

ROOT  := ../..
FLAGS := -Q . "" -Q $(ROOT)/proofs/lib fvzlib.proofs.lib \
         -Q $(ROOT)/proofs/adler32 fvzlib.proofs.adler32 \
         -Q $(ROOT)/spec/format fvzlib.format -Q $(ROOT)/spec/api fvzlib.api
FILES := Twice

.PHONY: all clean
all:
	for f in $(FILES); do rocq compile $(FLAGS) $$f.v || exit 1; done
	python3 $(ROOT)/tools/check_axioms.py --flags '$(FLAGS)' .

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux
