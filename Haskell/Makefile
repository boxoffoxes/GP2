GHC=ghc -O2
GHC_PROF=$(GHC) -prof -fprof-auto -rtsopts

TARGETS=gp2 gp2c ViewGraph IsoChecker

all : tags $(TARGETS)

gp2c : GP2c.hs OILR4/CRuntime.hs
	$(GHC) -o $@ $<

test : gp2c
	cd Tests && ./run-tests.sh

OILR4/CRuntime.hs : OILR4/oilrrt.c
	touch OILR4/CRuntime.hs

gp2 : Main.hs
	$(GHC) -o $@ $<

% : %.hs
	$(GHC) $<

tags :
	echo ":ctags" | ghc -v0 Main.hs

clean :
	rm -f *.{o,hi} OILR4/*.{o,hi} $(TARGETS)

sloc : OILR4/oilrrt.c
	grep -v '\s*//' $< | grep -v '^\s*$$' | wc -l

.PHONY : gp2 gp2c
