CXX       = g++
PROF      = 
MAPF      = mapf
GEAS_ROOT = ../geas
ECBS_ROOT = ../ECBS_PF
CXXFLAGS    = -I include -Wall -Wno-deprecated
CXXFLAGS += --std=c++11
CXXFLAGS += -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS
CXXFLAGS += $(PROF)
LFLAGS    = -lz -Wall -Wno-deprecated
LFLAGS   += $(PROF)

PROF_FLAGS = 
#PROF_FLAGS = -pg

## ECBS flags
CXXFLAGS += -I $(ECBS_ROOT) -Wall -I /usr/include/boost/ -I /usr/local/lib -lboost_program_options -lboost_graph
## geas flags
CXXFLAGS += -I $(GEAS_ROOT)/include
#ECBS_LFLAGS = -L $(ECBS_ROOT) -L . -lboost_program_options -lboost_graph -lgeas -lecbs
LFLAGS += -L $(ECBS_ROOT) -L $(GEAS_ROOT) -L . -lboost_program_options -lboost_graph -lgeas -lecbs
LFLAGS += $(PROF_FLAGS)

COPTIMIZE = -O3 -march=native -ffast-math -funroll-loops # -freorder-blocks-and-partition
#COPTIMIZE = -O2
#COPTIMIZE = -O1
#COPTIMIZE = -O0
#COPTIMIZE += -DNDEBUG
COPTIMIZE += $(PROF_FLAGS)
CXXFLAGS += $(COPTIMIZE)
#CXXFLAGS += -ggdb -D DEBUG
CXXFLAGS += -g -ggdb

MAPF_SRCS     = $(wildcard lib/$(MAPF)/*.cc)
MAPF_OBJS     = $(addsuffix .o, $(basename $(MAPF_SRCS)))
MAPF_DEPS     = $(addsuffix .d, $(basename $(MAPF_SRCS)))

#TARGETS = $(TESTS)
#MLTARGETS = ml/libgeas_ml.a ml/geas.cma ml/geas.cmxa ml/geas.a
#FZN_TARGETS = fzn/fzn_geas fzn/fzn_geas.debug

TARGETS = lazy-cbs
LIBGEAS = libgeas.a
LIBECBS = libecbs.a
all: $(TARGETS)

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

#libgeas.a: $(GEAS_ROOT)/libgeas.a
#	cp $(GEAS_ROOT)/libgeas.a libgeas.a


#libecbs.a : $(ECBS_ROOT)/libecbs.a
#	cp $(ECBS_ROOT)/libecbs.a libecbs.a

lazy-cbs : lib/lazy-cbs.o $(MAPF_OBJS) $(LIB) $(ECBS)
#	@$(CXX) $^ $(LFLAGS) $(ECBS_LFLAGS) -o $@
  
## Clean rule
clean:
	@rm -f $(MAPF_OBJS) $(MAPF_DEPS) lib/lazy-cbs.o
clobber: clean
	@rm -f $(TARGETS)

-include $(MAPF_DEPS)
