CAML_PREFIX=$(dir $(shell which ocamlc))/..
CAMLIDL_PREFIX=$(dir $(shell which camlidl))/..
OCAMLC=$(CAML_PREFIX)/bin/ocamlc.opt
OCAMLOPT=$(CAML_PREFIX)/bin/ocamlopt.opt
OCAMLMKTOP=$(CAML_PREFIX)/bin/ocamlmktop.opt
OCAMLDEP=$(CAML_PREFIX)/bin/ocamldep.opt
OCAMLLEX=$(CAML_PREFIX)/bin/ocamllex.opt
OCAMLYACC=$(CAML_PREFIX)/bin/ocamlyacc.opt

#---------------------------------------
# Directories
#---------------------------------------

SRCDIR = $(shell pwd)
#
# Installation directory
#
SITE-LIB = $(shell $(OCAMLFIND) printconf destdir)
PKG-NAME = fzn_geas
SITE-LIB-PKG = $(SITE-LIB)/$(PKG-NAME)

#---------------------------------------
# CAML part
#---------------------------------------

MLMODULES=\
   dynArray \
	 opts \
   util dom token problem \
	 simplify \
	 polarity half_reify \
   registry check \
   build \
   fznLexer fznParser

OCAMLINC=-I ../ml

OCAMLFLAGS+=$(OCAMLINC)
OCAMLOPTFLAGS+=$(OCAMLINC)

#PROF = -ccopt "-pg" -p
PROF =
OCAMLOPTFLAGS+=$(PROF)

#---------------------------------------
# Rules
#---------------------------------------

# Global rules
#TESTS=testPath testInterpret testLexer
TARGETS=fzn_geas
TARGETS_BYTE=$(TARGETS:%=%.byte)
TARGETS_PROF=$(TARGETS:%=%.p)
TARGETS_DEBUG=$(TARGETS:%=%.debug)

TESTS=$(basename $(wildcard tests/*.ml))
TESTS_BYTE=$(TESTS:%=%.byte)
TESTS_PROF=$(TESTS:%=%.p)
TESTS_DEBUG=$(TESTS:%=%.debug)

#all: opt byte
all: opt fzn_geas_top

#byte: $(TARGETS_BYTE) $(TESTS_BYTE)
#opt: $(TARGETS) $(TESTS)
#prof: $(TARGETS_PROF) $(TESTS_PROF)
#debug: $(TARGETS_DEBUG) $(TESTS_DEBUG)
byte: $(TARGETS_BYTE)
opt: $(TARGETS)
prof: $(TARGETS_PROF)
debug: $(TARGETS_DEBUG)

#$(TARGETS_BYTE) : %.byte : $(MLMODULES:%=%.cmo) %.ml
#	$(OCAMLFIND) ocamlc $(OCAMLFLAGS) -o $@ $(subst .byte,.mli,$@)  $^ -package $(REQ_PKG) -linkpkg

#libgeas_ml.a : ../ml/libgeas_ml.a
#	cp ../ml/libgeas_ml.a .

$(TARGETS) : geas.a libgeas_ml.a
$(TARGETS_DEBUG) : geas.a libgeas_ml.a

geas.a: ../ml/geas.a
	cp ../ml/geas.a .
libgeas_ml.a: ../ml/libgeas_ml.a
	cp ../ml/libgeas_ml.a .

$(TARGETS) : % : $(MLMODULES:%=%.cmx) %.ml
#	$(OCAMLFIND) ocamlopt $(OCAMLOPTFLAGS) -o $@ 
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ \
  -ccopt "-L $(CAML_PREFIX)/lib/ocaml -L $(CAMLIDL_PREFIX)/lib/camlidl" \
  ../ml/geas.cmxa \
  $@.mli $^

$(TARGETS_DEBUG) : %.debug : $(MLMODULES:%=%.cmo) %.ml
#	$(OCAMLFIND) ocamlc $(OCAMLFLAGS) -custom -g -o $@
	$(OCAMLC) $(OCAMLFLAGS) -custom -g -o $@ \
  -ccopt "-L $(CAML_PREFIX)/lib/ocaml -L $(CAMLIDL_PREFIX)/lib/camlidl" \
  ../ml/geas.cma \
  $(subst .debug,.mli,$@)  $^

$(TARGETS_PROF) : %.p : $(MLMODULES:%=%.p.cmx) %.ml
	#$(OCAMLFIND) ocamlopt -p $(OCAMLFLAGS) -o $@ 
	$(OCAMLOPT) -p $(OCAMLFLAGS) -o $@ \
  -ccopt "-L $(CAML_PREFIX)/lib/ocaml -L $(CAMLIDL_PREFIX)/lib/camlidl" \
  ../ml/geas.cmxa \
  $(subst .p,.mli,$@) $^

fzn_geas_top : $(MLMODULES:%=%.cmo)
	$(OCAMLMKTOP) $(OCAMLFLAGS) -custom -o $@ \
	../ml/geas.cma \
  $(MLMODULES:%=%.cmo) \
  -ccopt "-ggdb" \
  -ccopt "-L $(CAML_PREFIX)/lib/ocaml -L $(CAMLIDL_PREFIX)/lib/camlidl" \
	-ccopt "-L . -L ../ml -L ../lib " -cclib "-lcamlidl -lstdc++ -lgeas_ml"

clobber: clean
	/bin/rm -f Makefile.depend TAGS
	/bin/rm -f $(TARGETS) $(TARGETS_BYTE) $(TARGETS_PROF) $(TARGETS_DEBUG)

clean:
	/bin/rm -f *.cm[ioxat] *.cmti *.o *.cmxa *.annot *.html *.ps *.pdf *.dvi *.out
	/bin/rm -f fznLexer.ml
	/bin/rm -f *.aux *.bbl *.blg *.dvi *.pdf *.log *.toc *.idx *.ilg *.ind ocamldoc*.tex ocamldoc.sty

wc: $(SRC)
	wc $^

#--------------------------------------------------------------
# IMPLICIT RULES AND DEPENDENCIES
#--------------------------------------------------------------

.SUFFIXES: .ml .mli .cmi .cmo .cmx

#-----------------------------------
# CAML
#-----------------------------------

%.ml: %.mll
	$(OCAMLLEX) $^

%.ml %.mli: %.mly
	$(OCAMLYACC) $^

%.cmi: %.mli
	$(OCAMLFIND) ocamlc $(OCAMLFLAGS)  -c $<

%.cmo: %.ml
	$(OCAMLFIND) ocamlc $(OCAMLFLAGS) -c $<

%.cmx: %.ml
	$(OCAMLFIND) ocamlopt $(OCAMLOPTFLAGS)  -c $<

%.p.cmx: %.ml
	$(OCAMLFIND) ocamlopt -p $(OCAMLOPTFLAGS)  -c -o $@ $<

.PHONY: tags TAGS
tags: TAGS
TAGS: $(MLMODULES:%=%.mli) $(MLMODULES:%=%.ml)
#	ocamltags $^
	otags $^

.PHONY: depend cpp
depend:
	$(OCAMLDEP) $(MLMODULES:%=%.mli) $(MLMODULES:%=%.ml) >Makefile.depend

Makefile.depend:
	$(OCAMLDEP) $(MLMODULES:%=%.mli) $(MLMODULES:%=%.ml) >Makefile.depend

-include Makefile.depend
