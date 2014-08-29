# a list of all the programs in your project
PROGS = ProbReach
# a list of all your units to be linked with your programs (space separated)
OTHERS = Entry Integral Distribution RV CartesianProduct
# directory where capd scripts are (e.g. capd-config)
CAPDBINDIR =/home/b2049657/capd-4/bin/
# setting compiler and linker flags
CAPDFLAGS = `${CAPDBINDIR}capd-config --cflags`
CAPDLIBS = `${CAPDBINDIR}capd-config --libs`
CXXFLAGS += ${CAPDFLAGS} -O2 -Wall -std=c++11
# directory where object and dependancy files will be created
OBJDIR = .obj/
#============ the following should not be changed =========
OTHERS_OBJ = ${OTHERS:%=${OBJDIR}%.o}
OBJ_FILES = ${OTHERS_OBJ} ${PROGS:%=${OBJDIR}%.o}
.PHONY: all
all: ${PROGS}
# rule to link executables
${PROGS}: % : ${OBJDIR}%.o ${OTHERS_OBJ}
	${CXX} -o $@ $< ${OTHERS_OBJ} ${CAPDLIBS}
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
	./../bin/${PROGS} ../example/bouncing-ball-settings.txt
