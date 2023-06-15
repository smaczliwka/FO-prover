.PHONY: all

all: FO-prover

FO-prover: FO-prover.hs *.hs
	ghc -o FO-prover -O3 FO-prover.hs

clean:
	rm FO-prover *.hi *.o