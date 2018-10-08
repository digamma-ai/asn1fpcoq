LIBNAME := asn1fpcoq

.SUFFIXES:

.PHONY: default config clean clean-dep distclean clean-doc tags doc install-doc install-dist targz wc extracted

MAKECOQ := +$(MAKE) -r -f Makefile.coq
COQPKGFLAGS := -R ASN ASN -R Aux Aux -R Conversion Conversion -R IEEE IEEE

COQEXEC="$(COQBIN)coqtop" -q -w none $(COQINCLUDES) $(COQPKGFLAGS) -batch -load-vernac-source

LIBVFILES := Aux/StructTactics.v

VFILES := $(shell find . -name \*.v | grep -v .\#  | grep -v ml/ | cut -c 3- )
#VFILES := $(COQFILES:%=coq/%.v)
VOFILES := $(COQFILES:%=coq/%.vo)

MYVFILES := $(filter-out $(LIBVFILES), $(VFILES))

# OCaml sources
MLDIR = ml
EXTRACTDIR = ml/extracted
TSTAMP = $(EXTRACTDIR)/.timestamp

default: Makefile.coq 
	$(MAKECOQ)

extracted: $(TSTAMP)

$(TSTAMP): $(VOFILES) $(EXTRACTDIR)/Extract.v
	@echo "Extracting"
	rm -f $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli
	$(COQEXEC) $(EXTRACTDIR)/Extract.v
	touch $(TSTAMP)

install-dep:
	opam instal coq coq-flocq

config Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject $(VFILES) -o Makefile.coq

clean:
	rm -f `find . -name \*~`
	-$(MAKECOQ) clean
	rm -rf `find . -name .coq-native -o -name .\*.aux -o -name \*.time -o -name \*.cache`

clean-dep:
	rm -f `find . -name \*.v.d`

distclean: clean clean-dep clean-doc
	rm -f Makefile.coq Makefile.coq.conf

clean-doc:
	rm -f doc/$(LIBNAME).* doc/index.html doc/main.html coqdoc.sty coqdoc.css

doc: $(MYVFILES)
	coqdoc --html  --utf8 -d doc -R . $(LIBNAME) $(MYVFILES)
	coqdoc --latex --utf8 -d doc -R . $(LIBNAME) $(MYVFILES)

wc:
	coqwc $(MYVFILES)

%.vo: %.v
	$(MAKECOQ) $@

%:
	$(MAKECOQ) $@

