# DBG=1
# Choose solver (MiniSat or Glucose)
USE_GL=1
# Choose version (minisat_simp, glucose_parallel for USE_SIMP=0)
USE_SIMP=1

CSRCS    = $(wildcard ./src/*.cc)
NSRCS    = $(wildcard *.nw)
YACC     = $(wildcard *.y)
LEX      = $(wildcard *.l)
COBJS    = $(CSRCS:.cc=.o) $(YACC:.y=.tab.o) $(LEX:.l=.o)
DEPENDS = ${COBJS:.o=.d}
PDFS    = $(NSRCS:.nw=.pdf)
LIBD =
LIBS =
EXE = claussat
CXX?=g++
CC=g++

CFLAGS+=-I.

ifdef PROF
CFLAGS+=-fprofile-arcs -ftest-coverage
CFLAGS+=-pg
CFLAGS+=-g
LNFLAGS+=-fprofile-arcs
LNFLAGS+=-pg
LNFLAGS+=-g
endif


ifdef DBG
CFLAGS+=-O0
CFLAGS+=-ggdb
CFLAGS+=-DDBG
CFLAGS+=-g3
MSAT=libd
else
CFLAGS+=-DNDEBUG
CFLAGS+=-O3
MSAT=libr
endif



ifdef NOO
CFLAGS+=-O0
endif

CFLAGS += -Wall -DBUILDDATE='"$(BUILDDATE)"' -DDISTDATE='"$(DISTDATE)"'
CFLAGS += -DCHANGESET='"$(CHANGESET)"' -DRELDATE='"$(RELDATE)"'
CFLAGS+=-D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS -Wno-parentheses -Wno-deprecated -Wno-misleading-indentation -D _MSC_VER
#CFLAGS+=-std=c++11
CFLAGS+=-std=c++0x
CFLAGS+=-MMD
LIBS+=-lz

# Glucose: No core version after glucose 4.0
ifdef USE_GL
EXTERNAL+=gl
CFLAGS+=-I./src/glucose-4.1/
LIBD+=-L./src/glucose-4.1/simp
LIBD+=-L./src/glucose-4.1/parallel
LIBS+=-lglucose_simp
LIBS+=-lglucose_parallel
CFLAGS+=-DUSE_GL
else
EXTERNAL+=m
LIBS+=-lminisat
LIBS+=-lminisat_simp
LIBD+=-L./src/minisat/core
LIBD+=-L./src/minisat/simp
CFLAGS+=-I./src/minisat/
endif

ifdef EXPERT # allow using giving options, without options the solver's fairly dumb
CFLAGS+=-DEXPERT
endif

ifdef STATIC
CFLAGS+=-static
LNFLAGS+=-static
endif

ifdef USE_SIMP
CFLAGS+=-DUSE_SIMP
endif

ifdef NON_INCR
CFLAGS+=-DNON_INCR
endif

## Filter used to typeset C++
NW_FILTER=-filter C++.filter

.PHONY: m gl all doc

all:
	make $(EXE)

$(EXE):  $(COBJS) $(EXTERNAL)
	@echo Linking: $@
	@$(CXX) -o $@ $(COBJS) $(LNFLAGS) $(LIBD) $(LIBS)

m:
	@export MROOT=`pwd`/src/minisat ; cd ./src/minisat/core; make CXX=$(CXX) LIB=minisat $(MSAT)
	@export MROOT=`pwd`/src/minisat ; cd ./src/minisat/simp; make CXX=$(CXX) LIB=minisat_simp $(MSAT)

gl:
	@export MROOT=`pwd`/src/glucose-4.1 ; cd ./src/glucose-4.1/simp;     make CXX=$(CXX) LIB=glucose_simp $(MSAT)
	@export MROOT=`pwd`/src/glucose-4.1 ; cd ./src/glucose-4.1/parallel; make CXX=$(CXX) LIB=glucose_parallel $(MSAT)

sources: $(GENF)

main.o: main.cc

%.o:	%.cc
	@echo Compiling: $@
	@$(CXX) $(CFLAGS) -c -o $@ $<

%.o:	%.c Makefile
	@echo Compiling: $@
	@$(CXX) $(CFLAGS) -c -o $@ $<

%.tab.h %.tab.c: %.y
	@echo Generating: $*
	@bison $<

%.c:	%.l Makefile
	@echo Generating: $*
	@flex -o$@ $<

./src/Options.hh ./src/Options.cc: ./src/option_generation.py
	@echo Generating: $@
	python2 ./src/option_generation.py  >./src/Options.hh 2>./src/Options.cc

clean:
	@rm -f $(DEPENDS)
	@rm -f $(GENF)
	@rm -f $(EXE) $(EXE).exe $(COBJS) *.tab.[ch]
	@export MROOT=`pwd`/src/minisat ; cd ./src/minisat/core; make CXX=$(CXX) clean
	@export MROOT=`pwd`/src/minisat ; cd ./src/minisat/simp; make CXX=$(CXX) clean
	@export MROOT=`pwd`/src/glucose-4.1 ; cd ./src/glucose-4.1/simp    ; make CXX=$(CXX) clean
	@export MROOT=`pwd`/src/glucose-4.1 ; cd ./src/glucose-4.1/parallel; make CXX=$(CXX) clean

doc: $(PDFS)

%.pdf:  doc/%.tex
	@latexmk -pdf $<

doc/%.tex:  doc/%.nw doc/texheader.tex Makefile
	@noweave -x $(NW_FILTER) $< | sed 's/\\begin{document}/\\input{doc/texheader.tex}\\begin{document}/' >$@

-include ${DEPENDS}
