COQPROJECT_EXISTS=$(wildcard _CoqProject)

ifeq "$(COQPROJECT_EXISTS)" ""
$(error "Run ./configure before running make")
endif

default: Makefile.coq Main.hs
	$(MAKE) -f Makefile.coq
	ghc --make Main.hs -o Pretty

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean:
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq *.hi *.o Pretty Pretty.hs

.PHONY: default clean
