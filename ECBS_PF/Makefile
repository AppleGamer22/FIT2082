CXX = g++
CXXFLAGS = -fPIC -Wall -I /usr/local/lib -std=c++11
CXXFLAGS += -O3
CXXFLAGS += -DNDEBUG -shared
#CXXFLAGS += -O2 -g -pg
#CXXFLAGS += -O2 -g
#CXXFLAGS += -O0 -g

default: libecbs.so

compute_heuristic.o: compute_heuristic.cpp compute_heuristic.h
	$(CXX) $(CXXFLAGS) -c compute_heuristic.cpp

map_reader.o: map_loader.cpp map_loader.h
	$(CXX) $(CXXFLAGS) -c map_loader.cpp

agents_loader.o: agents_loader.cpp agents_loader.h
	$(CXX) $(CXXFLAGS) -c agents_loader.cpp

egraph_reader.o: egraph_reader.cpp egraph_reader.h
	$(CXX) $(CXXFLAGS) -c egraph_reader.cpp
node.o: node.cpp node.h
	$(CXX) $(CXXFLAGS) -c node.cpp

single_agent_ecbs.o: single_agent_ecbs.cpp single_agent_ecbs.h
	$(CXX) $(CXXFLAGS) -c single_agent_ecbs.cpp

clean:
	rm -rf *o *~ driver.log core

clobber: clean
	rm -rf libecbs.a

libecbs.so : map_loader.o agents_loader.o egraph_reader.o compute_heuristic.o node.o single_agent_ecbs.o
	@echo Building libecbs.so
	@ar rc $@ $^
	@ranlib $@

make_tags:
	echo "find . -maxdepth 1 -regex '.*/.*\.\(c\|cpp\|h\|cxx\)$' -print | etags -"
