CXX := clang++-12
CXXFLAGS := $(shell llvm-config-12 --cxxflags) 
LLVMLDFLAGS := $(shell llvm-config-12 --ldflags --libs) -ldl

SOURCES = occ2flx.cpp
OBJECTS = $(SOURCES:.cpp=.o)
EXES = $(OBJECTS:.o=)
CLANGLIBS = \
  -lclangTooling \
  -lclangFrontend \
  -lclangDriver \
  -lclangBasic \
  -lclang-cpp

all: $(OBJECTS) $(EXES)
.PHONY: clean install

%: %.o
	$(CXX) -o $@ $< $(LLVMLDFLAGS) $(CLANGLIBS) 


clean:
	-rm -f $(EXES) $(OBJECTS) n a.out *~

