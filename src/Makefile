# setting a compiler
CXX = g++-4.9
CC = gcc-4.9
# a list of all the programs in your project
PROGS = ProbReach
# a list of all your units to be linked with your programs (space separated)
#OTHERS = PartialSum Integral RVIntegral MulRVIntegral DecisionProcedure FileParser Box RV nRV BoxFactory
OTHERS = PartialSum Integral RVIntegral FileParser RV DD Box MulRVIntegral BoxFactory DecisionProcedure
# directory where capd scripts are (e.g. capd-config)
CAPDBINDIR =/home/fedor/capd-4/bin/
# to use CAPD4 which comes with dReal distribution
#CAPDBINDIR = /Users/b2049657/dreal-master/build/release/bin/
# setting compiler and linker flags
IBEXFLAGS = `pkg-config --cflags ibex`
IBEXLIBS = `pkg-config --libs ibex`
CAPDFLAGS = `${CAPDBINDIR}capd-config --cflags`
CAPDLIBS = `${CAPDBINDIR}capd-config --libs`
CXXFLAGS += ${CAPDFLAGS} ${IBEXFLAGS} -fopenmp -O2 -Wall -std=c++11
# !!! FLAGS -static AND -fopenmp DO NOT WORK ON OS-X/Clang
# Works on Linux/g++
LDFLAGS = -fopenmp -static
# Works on OS-X/g++
#LDFLAGS = -fopenmp -static-libgcc -static-libstdc++
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

install:
	mkdir -p ../bin
	cp ${PROGS} ../bin
	rm ${PROGS}

test:
	../bin/${PROGS} --verbose ../model/starvation/starvation.pdrh --dreach -l 0 -k 0 -z
