# a list of all the programs in your project
PROGS = src/ProbReach
# a list of all your units to be linked with your programs (space separated)
OTHERS = src/Entry src/Integral src/Distribution src/RV src/CartesianProduct
# directory where capd scripts are (e.g. capd-config)
CAPDBINDIR =/home/fedor/dreal-2.14.06/build/release/bin/
# setting compiler and linker flags
CAPDFLAGS = `${CAPDBINDIR}capd-config --cflags`
CAPDLIBS = `${CAPDBINDIR}capd-config --libs`
CXXFLAGS += ${CAPDFLAGS} -O2 -Wall
LDFLAGS = -lboost_regex -L/home/fedor/boost_1_55_0
# directory where object and dependancy files will be created
OBJDIR = .obj/
#============ the following should not be changed =========
OTHERS_OBJ = ${OTHERS:%=${OBJDIR}%.o}
OBJ_FILES = ${OTHERS_OBJ} ${PROGS:%=${OBJDIR}%.o}
.PHONY: all
all: ${PROGS}
# rule to link executables
${PROGS}: % : ${OBJDIR}%.o ${OTHERS_OBJ}
	${CXX} -o $@ $< ${OTHERS_OBJ} ${CAPDLIBS} ${LDFLAGS}
# include files with dependencies
-include ${OBJ_FILES:%=%.d}
#rule to compile .cpp files and generate corresponding files with dependencies
${OBJ_FILES}: ${OBJDIR}%.o : %.cpp
	@mkdir -p ${OBJDIR}
	${CXX} ${CXXFLAGS} -MT $@ -MD -MP -MF ${@:%=%.d} -c -o $@ $<
# rule to clean all object files, dependencies and executables
.PHONY: clean
clean:
	rm -f ${OBJDIR}*.o ${OBJDIR}*.o.d ${PROGS}