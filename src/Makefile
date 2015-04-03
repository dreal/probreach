# obtaining OS kernel name
OS := $(shell uname -s)

# a list of all the programs in your project
PROGS = ProbReach

# a list of all your units to be linked with your programs (space separated)
OTHERS = PartialSum Integral RVIntegral FileParser RV DD Box MulRVIntegral BoxFactory DecisionProcedure CSVParser

# obtaining ibex flags
IBEXFLAGS = `pkg-config --cflags ibex`
IBEXLIBS = `pkg-config --libs ibex`

# obtaining capd flags
CAPDFLAGS = `${CAPDBINDIR}capd-config --cflags`
CAPDLIBS = `${CAPDBINDIR}capd-config --libs`

# composing c++ flags
CXXFLAGS += ${CAPDFLAGS} ${IBEXFLAGS} -O2 -Wall -std=c++11

# in case if compiling with OpenMP
ifeq (${WITHOMP},yes)
	CXXFLAGS += -fopenmp
	LDFLAGS += -fopenmp
endif

# in case if compiled on Linux
ifeq (${OS},Linux)
	LDFLAGS += -static
endif
# in case if compiled on Mac OS X
ifeq (${OS},Darwin)
	LDFLAGS += -static-libgcc -static-libstdc++
endif
# in cases if none of the above static option is not used

# directory where object and dependancy files will be created
OBJDIR = .obj/

#============ the following should not be changed =========
OTHERS_OBJ = ${OTHERS:%=${OBJDIR}%.o}
OBJ_FILES = ${OTHERS_OBJ} ${PROGS:%=${OBJDIR}%.o}

.PHONY: all
all: ${PROGS}
# rule to link executables
${PROGS}: % : ${OBJDIR}%.o ${OTHERS_OBJ}
	${CXX} ${LDFLAGS} -o $@ $< ${OTHERS_OBJ} ${CAPDLIBS} ${IBEXLIBS}
# include files with dependencies
-include ${OBJ_FILES:%=%.d}
#rule to compile .cpp files and generate corresponding files with dependencies
${OBJ_FILES}: ${OBJDIR}%.o : %.cpp
	@mkdir -p ${OBJDIR}
	${CXX} ${CXXFLAGS} -MT $@ -MD -MP -MF ${@:%=%.d} -c -o $@ $<

# rule to clean all object files, dependencies and executables
.PHONY: clean
clean:
	rm -f ${OBJDIR}*.o ${OBJDIR}*.o.d ../bin/${PROGS}

.PHONY: install
install:
	mkdir -p ../bin
	cp ${PROGS} ../bin
	rm ${PROGS}

