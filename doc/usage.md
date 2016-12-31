# File format

See below the content of `stop-nonlinear.pdrh`.
```
model: npha;
/*
 * The model of a car deceleration scenario
 */
#define v_max 55.56 // [200 km/h] maximum speed of a car (m/s)
#define v_100 27.78 // m/s
#define drag 3.028e-4 // some average value (1/m)
#define mu 1
#define alpha 0.05776 
#define t_react 1.2

[0,1000] s; // distance m
[0,v_100] v; // velocity m/s (16.67 m/s = 60 km/h)
[0,30] tau; // time in seconds
[0,30] time;
[4.0,6.0] a_d;
dist_normal(4,0.1) beta;

// accelerating
{
mode 1;
flow:
d/dt[s]= v;
d/dt[v]= alpha*exp(-alpha*tau+beta)-drag*v*v;
d/dt[tau]= 1.0;
jump:
(and (v >= v_100))==>@2(and(s'=s)(v'=v)(tau'=0)(beta'=beta)(a_d'=a_d));
}

// reacting
{
mode 2;
flow:
d/dt[s]= v;
d/dt[v]= -drag*v*v;
d/dt[tau]= 1.0;
jump:
(and (tau = t_react))==>@3(and(s'=s)(v'=v)(tau'=0)(beta'=beta)(a_d'=a_d));
}

// braking
{
mode 3;
flow:
d/dt[s]= v;
d/dt[v]= -a_d-drag*v*v;
d/dt[tau]= 1.0;
jump:
(and (v <= 0))==>@4(and(s'=s)(v'=v)(tau'=0)(beta'=beta)(a_d'=a_d));
}

// stopped
{
mode 4;
flow:
d/dt[s]= v;
d/dt[v]= 0.0;
d/dt[tau]= 1.0;
jump:

}

init:
@1(and (s = 0) (v = 0) (tau = 0));

goal:
@4(and(tau=0)(s>=400));
```

## Model types

**ProbReach** performs automatic identification of the model type. However, it is recommended that the user specifies the model type explicitly. The available model types are:
* `model:ha` - specifies a deterministic hybrid system (*i.e.* the one not featuring any parameters).
* `model:pha` - specifies a parametric hybrid system featuring only random (*e.g.* discrete and/or continuous) parameters.
* `model:npha` - specifies a parametric hybrid system featuring both random and continuous nondeterministic parameters.

## Constants declaration

There are two possible ways of declaring a constant in the model:
* Using a C preprocessor macro `#define <var> <value>`. This could also be used to define functions 
* Alternative way of defining a constant is `[<value>]<var>;`

## Variable declaration

In order to define a variable or a continuous nondeterministic parameter one must provide its name and range as `[<value>,<value>]<var>;`.

## Random parameter declaration

The continuous nondeterministic parameters are declared in the same way as variables. The difference between a variable and a parameter in the model is that every variable has dynamics associated with further in the modes definition as opposed to the parameters.

The random parameters are defined using a key word. The following distribution are available:
* `dist_normal(<value>,<value>)<var>;` - defines a normal random parameter `<var>` where the first `<value>` is the mean and the second `<value>` is the standard deviation of the distribution.
* `dist_uniform(<value>,<value>)<var>;` - defines a uniform random parameter `<var>` where the first `<value>` is the minimum and the second `<value>` is the maximum values of the uniform distribution.
* `dist_exp(<value>)<var>;` - defines an exponential random parameter `<var>` where the `<value>` is the rate value of the exponential distribution.
* `dist_discrete(<value>:<value>[,<value>:<value>])<var>;` - defines a discrete random parameter `<var>` where for each pair `<value>:<value>` the second `<value>` corresponds to the probability mass associated with the first `<value>`.
* `dist_gamma(<value>,<value>)<var>;` - defines a gamma random parameter `<var>` where the first `<value>` is the shape and the second `<value>` is the scale of the gamma distribution.

Also it is possible to define continuous random parameters which probability density functions are nontrivial. Such parameter can be defined as:
* `dist_pdf(<fun>,<value>,<value>,<value>)<var>;` - defines a continuous random parameter `<var>` which probability density function (PDF) is defined by `<fun>`. The PDF must be written in the infix notation. The first `<value>` and the second `<value>` define the minimum and the maximum value of `<var>`. In case if a distribution has unbounded support the keywords `-infty` and `infty` can be used. The fourth `<value>` is needed when the distribution has unbounded support. It defines a point from where the integration will be performed in both directions in order to enclose the defined unbounded random variable. For more information about how the unbounded continuous random parameters are handled see [reference]. For example, a normal random variable `x` with the mean `1.0` and standard deviation `0.1` can be defined using `dist_pdf` as: `dist_pdf((1/(0.1*sqrt(2*3.14159265359)))*exp(-(x-1)*(x-1)/(2*0.1*0.1)),-infty,infty,1.0) x;`.

## Defining modes

Every mode defines a discrete state of the system. The continous dynamics are defined inside the mode.
```
{
mode <id>;

flow:
d/dt[<var1>] = <ode1>;
...
d/dt[<varN>] = <odeN>;

jump:
<guard1>==>@<next_id1><reset1>;
...
<guardM>==>@<next_idM><resetM>;
}
```
* `mode <id>;` - defines the `<id>` of the mode.
* `flow:` - starts definition of the continuous dynamics of the system. It is followed by the list of ODEs in the form `d/dt[<var>] = <ode>;` where `<var>` is the name of the variable and `<ode>` is the ODE associated with `<var>`. All ODEs should be written in the infix notation.
* `jump:` - starts definition of the discrete transitions from the current state. It is followed by the list of discrete transitions in the form `<guard>==>@<next_id><reset>;` where `<guard>` defines the condition when the system may take a transition to mode `<next_id>` setting the initial value of the continuous dynamics in mode `<next_id>` as specified in `<reset>`.
    * each `<guard>` - is the quantifier free first order formula. The best way of doing this is to write `<guard>` in the disjunctive normal form as `(or (and (<expr> <op> 0) ... ) ... (and (<expr> <op> 0) ... ))` where each `expr` is a mathematical expression written in infix notation and each `<op>` is a comparison operator from the list `{<,<=,>,>=,=}`.
    * each `<reset>` - is the quantifier free first oreder formula in the form `(and (<var>'=<expr>) ...)` where `<var>'` is the initial value of `<var>` in mode `<next_id>` and `expr` is a mathematical expression written in infix notation.

## Defining the initial state

The initial state of the system is defined using the keyword `init:` followed by `@<id>(and (<var>=<expr>) ...)` where `<id>` is the id of the initial mode and each `(<var>=<expr>)` specifies the initial value of the variable `<var>`. Currently, **ProbReach** supports a single initial state.

## Defining the goal state

The goal state of the system is defined using the keyword `goal:` followed by `@<id>(or (and (<expr> <op> 0) ... ) ... (and (<expr> <op> 0) ... ))` where `<id>` is the id of the goal mode and `(or (and (<expr> <op> 0) ... ) ... (and (<expr> <op> 0) ... ))` is the quantifier free formula in disjunctive normal form. Currently, **ProbReach** supports a single goal state.

# How to run:
    ProbReach <options> <file.pdrh/file.drh> <solver-options>

## Command Line Options
In order to see the list of `<solver-options>` run `dReal --help`. The following options are available in `ProbReach`.

#### general options:

    -h/--help - displays help message
    -k <int> - defines the reachability depth (default: the shortest path length if exists)
    -l <int> - defines the reachability depth lower bound (cannot be used without -u; default: the shortest path length if exists)
    -u <int> - defines the reachability depth upper bound (cannot be used without -l; default: the shortest path length if exists)
    -t <int> - number of CPU cores (default: maximum number of CPU cores)
    --verbose - outputs computation details (default false)
    --verbose-result - outputs the runtime and the number of samples (statistical model checking only; default false)
    --version - displays current version of the tool

#### solver related options:
   
    --delta-sat - uses the delta-sat answer of dReal to conclude about satisfiability of the evaluated formula (statistical model checking and hybrid automata only; default false)
    --solver <path> - full path to the solver

#### special options:

    --time-var-name <string> - the name of the variable representing time in the model (default tau)

#### statistical model checking options:

    --bayesian-acc <double> - half-length of the confidence interval in Bayesian estimations (default: 0.01)
    --bayesian-conf <double> - confidence value in Bayesian estimations (default: 0.99)
    --cross-entropy - enables Cross-Entropy algorithm
    --cross-entropy-term-arg <double> - termination argument (variance) for Cross-Entropy algorithm (default: 0.01)
    --chernoff-acc <double> - half-length of the confidence interval in Chernoff-Hoeffding method (default: 0.01)
    --chernoff-conf <double> - confidence value in Chernoff-Hoeffding method (default: 0.99)
    --elite-ratio <double> - defines the fraction of the sample size - elite samples which are used in Cross-Entropy algorithm for updating the distribution parameters.
    --min-prob - computes confidence interval for the minimum reachability probability (default: maximum reachbility probability)
    --sample-size <int> - number of sample per iteration of Cross-Entropy algorithm
    
#### formal method options:

    -e/--precision-prob <double> - length of the probability enclosure (default: 0.001)
    --integral-inf-coeff <double> - ratio for the continuous random variables with unbounded support (default: 0.1)
    --integral-pdf-step <double> - step value used for bounding domains of unbounded continuous random variables (default 0.1)
    --partition-nondet - partitions the domain nondeterministic parameters up to the value defined in --precision-nondet (default: false)
    --partition-prob - obtains a partition of the domain of continuous random parameters satisfying -e/--precision-prob (default: false)
    --precision-nondet [<var> <double>] - defines the precision vector for the nondeterministic parameters
    --precision-ratio <double> - used to define precision passed to the solver as "solver-precision = min-box-dimension * precision-ratio" (default: 0.001)


