# Analyses and transformations over Clight syntax trees, shared by the
# proofs.  Needs the pinned toolchain.  Only TickLogic needs VST.
#
#   make        compile
#   make clean  remove build products

FILES := Census Guard Ticks TickLogic

.PHONY: all clean
all:
	for f in $(FILES); do rocq compile -Q . fvzlib.proofs.lib $$f.v || exit 1; done

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux
