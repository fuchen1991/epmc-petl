# EPMC-PETL: A Tool for Model Checking Probabilistic Multiagent Systems under Uniform Schedulers

## Introduction
EPMC-PETL is implemented as a plugin in ePMC(https://github.com/ISCAS-PMC/ePMC). It's a tool for model checking probabilistic multiagent systems under uniform schedulers, supporting PETL(Probabilistic Epistemic Temporal Logic). Two algorithms has been implemented: an exact algorithm based on SMT techniques and an approximated one based on UCT.

For more information about the algorithms, please visit https://www.ijcai.org/proceedings/2018/661.

## About the files
All the implementation details related to PETL model checking are under "epmc-petl/plugins/propertysolver-petl". 

You can find the experiment files used in the paper under "experiment_files". 

## Get the runnable jar file
You can download the runnable jar file from https://github.com/fuchen1991/epmc-petl/releases/tag/v1.0, or build it by yourself:

1. Dependencies: JDK 13.0+, Maven
 
2. Enter the main directory, run
 ```
 ./build.sh petl
 ```
Then you'll get our tool in an ALL-IN-ONE jar file epmc-petl.jar.

## Model, Property, and Equivalence relations

The models should be in the PRISM format(http://www.prismmodelchecker.org/manual/ThePRISMLanguage). Note that we redefine the composition of the modules to make the agents all take one local action in each transition, so the transitions from different modules will not synchronize according to the parallel composition operator.

The equivalence relations are described in this format:
```
equiv agent1
-- formula1;
-- formula2;
......
equiv end
equiv agent2
-- formula1;
-- formula2;
......
equiv end
......
......
```
Each agent in the model has a "equiv (agent name) ... equiv end" block, and each block contains a set of formulas. You can use the variables used in the model. All the states satisfying the same formula are regarded as equivalent by the agent. So you can not write formulas such that one state satisfies two or more formulas. If one state can not satisfy any formula, it's not equivalent to any other states.

The knowledge properties are described like this:
```
K {agent}  (state_formula)
E/C/D {agent1,..., agentn}  (state_formula)
```
Other properties can be described by the PRISM language(http://www.prismmodelchecker.org/manual/PropertySpecification).

You can find examples for these files under 'experiment_files'.

## Run
To run EPMC-PETL, you need JDK 13.0+ installed.

For SMT solvers, we test our tool with z3 4.6.0(https://github.com/Z3Prover/z3/releases/tag/z3-4.6.0).

There are two algorithms for PETL model checking, to run the algorithm which reduces the problem to MINLP, you can use the following command:
```
java -jar epmc-petl.jar check
--property-solver propositional-explicit,operator-explicit,pctl-explicit-next,petl-explicit-knowledge,petl-until-minlp
--prism-flatten false
--model-input-type mas
--property-input-type petl
--smtlib-command-line /path/to/z3-folder/bin/z3 -smt2 {0} 
--smtlib-version v25 
--constraintsolver-solver smt-lib-petl
--model-input-files /path/to/your-model /path/to/your-equivalence-relation 
--property-input-files /path/to/your-property
```
where you need to modify 4 paths: one for z3, one for the model file, one for equivalence relation file, and one for property file.


To run the algorithm based on UCT, you can use the following command:
```
java -jar epmc-petl.jar check
--property-solver propositional-explicit,operator-explicit,pctl-explicit-next,petl-explicit-knowledge,petl-until-uct
--prism-flatten false
--model-input-type mas
--property-input-type petl
--uct-depth-limit your-depth-limit
--uct-time-limit your-time-limit
--bvalue your-bvalue-coefficient
--print-time-interval your-print-time-interval
--random-seed your-random-seed
--model-input-files /path/to/your-model /path/to/your-equivalence-relation 
--property-input-files /path/to/your-property
```
where `uct-time-limit` means  how much time the solver should use when exploring the model(in seconds);  `uct-depth-limit` means how many steps the solver should perform in the state space exploration;  `bvalue` means the coefficient of the bias parameter in the UCT formula between old and new state exploration;  `print-time-interval ` means the algorithm should print the current result of the UCT search(in seconds); `random-seed` means the random seed used to select unvisited successors: you can set these parameters as you wish, and the default value of  `random-seed` is 1000, and all other default values are 1. Again, you need to specify the paths of the files.

## Examples
Let's take https://github.com/fuchen1991/epmc-petl/blob/master/experiment_files/navigation/same_initial/navigation_3_4.prism as the model file, and https://github.com/fuchen1991/epmc-petl/blob/master/experiment_files/navigation/navigation_1.equiv as the equivalence relation file. For property, we check `Pmin=? [F (at_goal1 | at_goal2)]`. 
 
 In this model, 2 robots move in a grid, trying to get to their goals. Each grid cell makes the robots disappear with a different probability. The robots are totally independent, and we're computing the minimal probability of at least one robot finally reaching its goal.

We put all these three files, the epmc-petl.jar file, and the z3-4.6.0 folder under the main directory, and run under this directory this command:
```
java -jar epmc-petl.jar check
--property-solver propositional-explicit,operator-explicit,pctl-explicit-next,petl-explicit-knowledge,petl-until-minlp
--prism-flatten false
--model-input-type mas
--property-input-type petl
--smtlib-command-line z3-4.6.0/bin/z3 -smt2 {0} 
--smtlib-version v25 
--constraintsolver-solver smt-lib-petl
--model-input-files navigation_3_4.prism navigation_1.equiv
--property-input-files navigation.property
```
The output is:
```
Running EPMC revision 81d3198e72cc538b29e2ad296e577c031a311301
Assertions are disabled. In case of incorrect results or otherwise strange behaviour, please run the JVM with "-ea" parameter.
Starting to parse PRISM model...
Done parsing PRISM model
Starting model checking...
Analysing property Pmin=? [F (at_goal1 | at_goal2)]
Starting to compute JANI explorer...
Starting to build initial states of JANI explorer...
Done building initial states of JANI explorer
Done building JANI explorer
Starting to build model...
Building model done. 196 states. Time for model exploration: 0 seconds.
Number of transitions:2194
Number of variables:300
Number of constraints:828
Call z3 to compute the minimal probability ...
Time required by z3: 2 seconds
Finished model checking. Time required: 3 seconds
Pmin=? [F (at_goal1 | at_goal2)]: 0.0000000
```

## Tips for developing

Although there is  a "epmc-constraintsolver-smt-lib" plugin, it's not enough for our MINLP problems. We change the classes "ConstraintSolverSMTLib", "InputWriter", and "OutputReader". And we  also copy "SMTLibOperator", "SMTLibResult", and "SMTLibVariable", because they are not public classes.  We use some other classes from  "epmc-constraintsolver-smt-lib", so  we need to add this plugin as a dependency. We call our new constraint solver as "smt-lib-petl".


"ModelMAS" is the class to store the model, where we change the composition of the modules. And "EquivalenceRelations" is the class for  equivalence relations.


The model checking algorithms are in the classes under epmc.propertysolver in the petl plugin.

## Contact
Comments and feedback about any this project are very welcome. Please contact:

Chen Fu

fchen###ios.ac.cn

