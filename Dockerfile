FROM dreal/dreal3
MAINTAINER Fedor Shmarov <f.shmarov@ncl.ac.uk>
RUN apt-get -y install libgsl0-dev
COPY . /usr/local/src/probreach
WORKDIR /usr/local/src/probreach
RUN mkdir -p /build/release
WORKDIR /usr/local/src/probreach/build/release
RUN cmake ../../
RUN make