FROM dreal/dreal3
MAINTAINER Fedor Shmarov <f.shmarov@ncl.ac.uk>
RUN apk add --no-cache g++
COPY bin/ProbReach /usr/local/bin/ProbReach
#ENTRYPOINT ProbReach
