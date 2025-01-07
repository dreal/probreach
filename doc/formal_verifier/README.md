# ProbReach Formal Verifier

The ProbReach verifier computes rigorous probability enclosures using exhaustive exploration of the system parameter space.

## Usage

	./formal_verifier <options> <file.pdrh/file.drh>

Some of the most frequently used options are shown below (alternatively, use -h flag to see all available options):
```
general options:
-t <int> - number of CPU cores (default: <max>)
-h/--help - displays help message
--solver <path> - full path to the solver
--verbose - outputs computation details (defualt: 0)
--version - displays current version of the tool

reachability options:
-k <int> - defines the reachability depth (should not be used together with options -l and -u; default: 0)
-l <int> - defines the reachability depth lower bound (should not be used without -u; default: 0)
-u <int> - defines the reachability depth upper bound (should not be used without -l; default: 0)

formal method options:
-e <double> - length of the probability enclosure (default: 0.001). The algorithm will try to refine the size of the reachabilty probability interval to be smaller or equal to the provided value. Note that when the system features nondeterministic parameter, the algorithm may never meet the required precision. Also, when --upper-bound flag is provided, option -e is ignored
--upper-bound - refine only the upper bound of the reachability probability (in this case the lower probability bound will be always set at 0) (default: 0)
--partition-prob <param1> <value1> ... - defines the precision values for computing a partition of the continuons random parameters
--partition-nondet <param1> <value1> ... - defines the precision values for computing a partition of the nondeterministic parameters
--precision-ratio <double> - used to define precision passed to the solver as (solver-precision = min-box-dimension * precision-ratio) (default: 0.001)
```


