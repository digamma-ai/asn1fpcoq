LIBNAME := asn1fpcoq

.SUFFIXES:

.PHONY: default config clean clean-dep distclean clean-doc tags doc install-doc install-dist targz wc extracted coq depend print-includes coq

# Coq sources
COQDIR = coq
COQLIBDIR = ../lib

# OCaml sources
MLDIR = ml
EXTRACTDIR = ml/extracted
TSTAMP = $(EXTRACTDIR)/.timestamp

COQINCLUDES=$(foreach d, $(COQDIR), -R $(d) ASN1FP) -R $(EXTRACTDIR) Extract

COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)
COQEXEC="$(COQBIN)coqtop" -q -w none $(COQINCLUDES) -batch -load-vernac-source

VFILES := $(shell find . -name \*.v | grep -v .\#  | grep -v ml/ | cut -c 3- )
VOFILES = $(VFILES:.v=.vo)

# OCaml sources
MLDIR = ml
EXTRACTDIR = ml/extracted
TSTAMP = $(EXTRACTDIR)/.timestamp

all: .depend
	$(MAKE) coq
	$(MAKE) extracted
	$(MAKE) $(EXE)

coq: $(VOFILES)

default: all

extracted: $(TSTAMP)

.depend: $(VFILES) 
	@echo "Analyzing Coq dependencies in" $(VFILES)
	@$(COQDEP) $^ > .depend

$(TSTAMP): $(VOFILES) $(EXTRACTDIR)/Extract.v
	@echo "Extracting"
	rm -f $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli
	$(COQEXEC) $(EXTRACTDIR)/Extract.v
	cp lib/big.ml $(EXTRACTDIR)/
	patch -p0 < lib/CRelationClasses.mli.patch
	touch $(TSTAMP)

install-dep:
	opam instal coq coq-flocq

config Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject $(VFILES) -o Makefile.coq

EXE=ml/_build/default/convtest.exe

$(EXE): extracted
	@echo "Compiling $(EXE)"
	(cd ml; dune build --profile=dev convtest.exe)

run: $(EXE)
	./$(EXE)

clean:
	rm -f `find . -name \*~`
	rm -rf `find . -name .coq-native -o -name .\*.aux -o -name \*.time -o -name \*.cache`
	rm -f .depend
	rm -f $(VOFILES)
	rm -rf doc/*.glob
	rm -f $(TSTAMP) $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli 
	rm -rf _build ml/_build $(EXTRACTDIR)/_build
	rm -f *.log *.cache

clean-dep:
	rm -f `find . -name \*.v.d`

print-includes:
	@echo $(COQINCLUDES)

distclean: clean clean-dep clean-doc
	rm -f Makefile.coq Makefile.coq.conf

clean-doc:
	rm -f doc/$(LIBNAME).* doc/index.html doc/main.html coqdoc.sty coqdoc.css

wc:
	coqwc $(VFILES)

%.vo: %.v
	@rm -f doc/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob doc/$(*F).glob $*.v

-include .depend
