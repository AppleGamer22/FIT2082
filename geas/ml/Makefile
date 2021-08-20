CAML_PREFIX=$(dir $(shell which ocamlc))/..
CAMLIDL_PREFIX=$(dir $(shell which camlidl))/..
OCAMLC=$(CAML_PREFIX)/bin/ocamlc.opt
OCAMLOPT=$(CAML_PREFIX)/bin/ocamlopt.opt
OCAMLMKTOP=$(CAML_PREFIX)/bin/ocamlmktop.opt
#PROF = -pg
PROF = 
#MLPROF = -ccopt "-pg" -p
MLPROF = 
CXX = g++
#CXX = g++-4.9
CXXFLAGS = -g -O3 -I ../include
CXXFLAGS += -Wall -Wno-non-virtual-dtor -Wno-unused-function -Wno-deprecated -ffast-math # -funroll-loops
#CXXFLAGS += -I /usr/local/lib/ocaml -I /opt/local/lib/ocaml
CXXFLAGS += -I $(CAML_PREFIX)/lib/ocaml -I $(CAMLIDL_PREFIX)/lib/camlidl
CXXFLAGS += $(PROF)
CFLAGS = -g -O3 -I ../include
CFLAGS += -Wall -Wno-unused-function -Wno-deprecated -ffast-math
#CFLAGS += -I /usr/local/lib/ocaml -I /opt/local/lib/ocaml
CFLAGS += -I $(CAML_PREFIX)/lib/ocaml -I $(CAMLIDL_PREFIX)/lib/camlidl
CFLAGS += $(PROF)
CFLAGS += -I ..
LFLAGS = -lz -L $(CAML_PREFIX)/lib/ocaml $(CAMLIDL_PREFIX)/lib/camlidl
LFLAGS += $(PROF)
OCAMLINC += -I ..
OCAMLOPTFLAGS += $(MLPROF)

## Shared library generation
SHARED = gcc -shared
RANLIB = ranlib

#IDLSRCS = $(wildcard *.idl)
IDLSRCS = atom.idl solver.idl internal.idl builtins.idl
MLIS = $(addsuffix .mli, $(basename $(IDLSRCS)))
MLS = $(addsuffix .ml, $(basename $(IDLSRCS)))
CMIS = $(addsuffix .cmi, $(basename $(IDLSRCS)))
CMOS = $(addsuffix .cmo, $(basename $(IDLSRCS)))
CMXS = $(addsuffix .cmx, $(basename $(IDLSRCS)))
STUBS = $(addsuffix _stubs.c, $(basename $(IDLSRCS)))
OBJS = $(addsuffix _stubs.o, $(basename $(IDLSRCS))) solver_extra.o
#DEPS = $(addsuffix .d, $(basename $(IDLSRCS)))

MLLIBS = geas

MLTARGETS = $(addsuffix .cma, $(MLLIBS)) $(addsuffix .cmxa, $(MLLIBS))
LIBTARGETS = libgeas_ml.a $(MLTARGETS)

all : $(LIBTARGETS) geas_top

#$(TESTS) : % : %.o $(OBJS)
#	$(CXX) $(CXXFLAGS) -o $@ $@.o $(OBJS) $(LFLAGS)

#libgeas.a:
#	cp ../libgeas.a .

$(STUBS) : $(MLIS)

%.ml %.mli : %.idl
	@echo Generating interfaces: " $^ "
	camlidl -no-include $^

geas.cma: $(CMIS) $(CMOS) libgeas_ml.a ../libgeas.a
	$(OCAMLC) $(OCAMLFLAGS) $(OCAMLINC) -custom -a -o $@ \
	$(CMOS) libgeas_ml.a ../libgeas.a \
	-ccopt "-L . -L ../lib" -cclib "-lcamlidl -lstdc++"

geas.cmxa geas.a: $(CMIS) $(CMXS) libgeas_ml.a ../libgeas.a
	$(OCAMLOPT) $(OCAMLOPTFLAGS) $(OCAMLINC) -a -o $@ \
	$(CMXS) libgeas_ml.a ../libgeas.a \
	-ccopt "-L . -L ../lib"  -cclib "-lcamlidl -lstdc++"
	$(RANLIB) geas.a

libgeas_ml.a: $(OBJS)
	$(AR) rcs $@ $^
	$(RANLIB) $@

libgeas_ml.so: $(OBJS)
	$(SHARED) -o $@ $^

geas_top : $(LIBTARGETS)
	$(OCAMLMKTOP) $(OCAMLINC) -custom -o $@ \
	geas.a geas.cma \
  -ccopt "-ggdb" \
  -ccopt "-L $(CAML_PREFIX)/lib/ocaml -L $(CAMLIDL_PREFIX)/lib/camlidl" \
	-ccopt "-L . -L ../lib " -cclib "-lcamlidl -lstdc++"

clean :
	rm -f $(TARGETS) $(TARGETOBJS) $(TESTOBJS) $(OBJS)
	rm -f $(MLIS) $(MLS) $(CMIS) $(CMOS) $(CMXS) $(STUBS)
	rm -f *.annot *.o

clobber : clean
	rm -f $(LIBTARGETS)

-include $(DEPS)
-include $(TARGETDEPS)

%.d: %.cpp
	@$(CXX) -MM -MT  $(subst .d,.o,$@) -MT $@ $(CPPFLAGS) $< > $@

#---------------------------------------
# ML generic rules
#---------------------------------------

%.cmi: %.mli  $(DEPS)
	$(OCAMLC) $(OCAMLFLAGS) $(OCAMLINC) -c $<

%.cmo: %.ml %.cmi  $(DEPS)
	$(OCAMLC) $(OCAMLFLAGS) $(OCAMLINC) -c $<

%.cmx: %.ml %.cmi  $(DEPS)
	$(OCAMLOPT) $(OCAMLOPTFLAGS) $(OCAMLINC) -c $<
