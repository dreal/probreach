**ProbReach** - collection of tools for computing probability of bounded reachability in hybrid systems with parametric uncertainties.

## How to build

```
sudo apt-get install git cmake build-essential bison flex libgsl-dev pkg-config libfl-dev
git clone https://github.com/dreal/probreach.git probreach
cd probreach
mkdir -p build/release
cd build/release
cmake ../../
make
```

## ProbReach tools

* [**simulator**](doc/simulator/README.md) - performs simulation of the provided ProbReach model.
* [**formal_verifier**](doc/formal_verifier/README.md) - computes rigorous probability enclosures using formal verification technique.
* [**mc_verifier**](doc/mc_verifier/README.md) - produces confidence intervals for the reachability probability via Monte Carlo sampling.
* [**pid_optimiser**](doc/pid_optimiser/README.md) - performs controller synthesis for sampled-data stochastic control systems.
* [**gp**](doc/gp/README.md) - estimates bounded reachability probability function via Gaussian process.
* [**pdrh2simulink**](doc/pdrh2simulink/README.md) - translates the provided ProbReach model into *Simulink®/Stateflow®* format.


## How to run tests
ProbReach uses [GoogleTest](https://github.com/google/googletest) for testing. Here is how you can set it up (click [here](https://github.com/google/googletest/blob/main/googletest/README.md) for more detailed instructions):
```
git clone https://github.com/google/googletest.git -b v1.15.2
cd googletest
mkdir build
cd build
cmake ../
make
sudo make install
```

Once GoogleTest is built and installed on your system, here is how you can use it to run ProbReach tests:
```
cd probreach/build/release
cmake ../../
make
make test
```
