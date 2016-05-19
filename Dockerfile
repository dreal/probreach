FROM dreal/dreal3
MAINTAINER Fedor Shmarov <f.shmarov@ncl.ac.uk>
WORKDIR /usr/local/src
RUN apt-get -y install libgsl0ldbl
COPY . probreach
RUN mkdir -p /usr/local/src/probreach/build/release
RUN cmake /usr/local/src/probreach/src
RUN make