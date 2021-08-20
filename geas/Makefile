CXX       = g++
#CXX       = g++-4.9
#CXX       = clang++
PROF      = 
#PROF      = -pg
MTL       = ./include/geas/mtl
ENGINE	  = ./lib/engine
SOLVER	  = ./lib/solver
CONSTRAINTS = ./lib/constraints
UTILS     = ./lib/utils
VARS      = ./lib/vars
CXXFLAGS    = -I ./include -Wall -Wno-deprecated -fno-rtti -fPIC # -ffloat-store
CXXFLAGS += --std=c++11
CXXFLAGS += -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS
CXXFLAGS += $(PROF)
LFLAGS    = -Wall -Wno-deprecated
LFLAGS   += $(PROF)

#CXXFLAGS += -DLOG_ALL
#CXXFLAGS += -DCACHE_WATCH
#CXXFLAGS += -DPVAL_32
#CXXFLAGS += -DPROOF_LOG
#CXXFLAGS += -DLOG_ALL
#CXXFLAGS += -DLOG_GC -DDEBUG_WMAP -DCHECK_STATE
#CXXFLAGS += -DDEBUG_WMAP
#CXXFLAGS += -DLOG_RESTART
#CXXFLAGS += -DLOG_GC
#CXXFLAGS += -DLOG_PROP
#CXXFLAGS += -DCHECK_STATE

COPTIMIZE = -O3 -march=native -ffast-math -funroll-loops # -freorder-blocks-and-partition
#COPTIMIZE = -O2
#COPTIMIZE = -O1
#COPTIMIZE = -O0
#COPTIMIZE += -DNDEBUG
CXXFLAGS += $(COPTIMIZE)
#CXXFLAGS += -ggdb -D DEBUG
CXXFLAGS += -g -ggdb

CSRCS     = $(wildcard $(ENGINE)/*.cc) $(wildcard $(VARS)/*.cc) $(wildcard $(SOLVER)/*.cc) $(wildcard $(CONSTRAINTS)/*.cc) $(wildcard $(CONSTRAINTS)/*/*.cc) $(wildcard $(UTILS)/*.cc)
COBJS     = $(addsuffix .o, $(basename $(CSRCS)))
CDEPS     = $(addsuffix .d, $(basename $(CSRCS)))

LIBSRCS = $(wildcard lib/c/*.cc)
LIBOBJS = $(addsuffix .o, $(basename $(LIBSRCS)))
LIBDEPS = $(addsuffix .d, $(basename $(LIBSRCS)))

#TESTS = tests/TestVars tests/TestChain
TESTS = 
TESTSRC = $(wildcard tests/*.cc)
TESTOBJS = $(addsuffix .o, $(basename $(TESTSRC)))
TESTS = $(basename $(TESTSRC))
TESTDEPS = $(addsuffix .d, $(TESTS))

TARGETS = $(TESTS)
MLTARGETS = ml/libgeas_ml.a ml/geas.cma ml/geas.cmxa ml/geas.a
FZN_TARGETS = fzn/fzn_geas fzn/fzn_geas.debug

#TARGETS = $(TESTS)
LIB = libgeas.a
all: $(TARGETS) $(LIB) $(MLTARGETS) $(FZN_TARGETS)

## Dependencies
$(TESTS) : % : %.o $(COBJS)

.PHONY: all clean tests

## Build rule
%.o:	%.cc %.d
	@echo Compiling: "$@ ( $< )"
	@$(CXX) $(CXXFLAGS) -c -o $@ $<

## Dependency rules.
### Note that this doesn't update dependencies if something new is
### introduced into an indirectly included header file.
%.d: %.cc
	@echo Building dependencies: "$@ ( $< )"
	@$(CXX) -MM -MT  $(subst .d,.o,$@) -MT $@ $(CXXFLAGS) $< > $@

## Linking rules
$(TARGETS):
	@echo Linking: "$@ ( $^ )"
	@$(CXX) $^ $(LFLAGS) -o $@

libgeas.a: $(COBJS) $(LIBOBJS)
	@echo Archiving: "$@ ( $^ )"
	ar rc $@ $^
	ranlib $@

ml/libgeas_ml.a ml/geas.a ml/geas.cmxa ml/geas.cma : libgeas.a
	@echo Building ML interface
	$(MAKE) -C $(@D) $(@F)

$(FZN_TARGETS) : % : $(LIB) $(ML_TARGETS) 
	@echo Building FZN interface
	$(MAKE) -C $(@D) $(@F)

## Clean rule
clean:
	$(MAKE) -C ml clean
	$(MAKE) -C fzn clean
	@rm -f $(TARGETS) $(LIB) geas.o $(COBJS) $(LIBOBJS) $(TESTOBJS) $(CDEPS) $(LIBDEPS) $(TESTDEPS)

clobber: clean
	$(MAKE) -C ml clobber
	$(MAKE) -C fzn clobber


-include $(CDEPS) $(LIBDEPS) $(TESTDEPS)
