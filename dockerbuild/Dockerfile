FROM dreal/dreal3-build
MAINTAINER Fedor Shmarov <f.shmarov@ncl.ac.uk>
VOLUME /usr/local/src/probreach/src
VOLUME /usr/local/src/probreach/bin
RUN apt-get -y install libgsl0-dev
RUN mkdir -p /usr/local/src/probreach/build/release
WORKDIR /usr/local/src/probreach/build/release
COPY build.sh .
ENTRYPOINT /bin/bash build.sh
