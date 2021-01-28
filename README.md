# Model Checking Probabilistic Multiagent Systems under Uniform Schedulers

## Introduction
Multiagent systems have found many applications in practice. We focus on probabilistic multiagent systems which can model uncertainty, such as component failure, of the agents and/or their environment. In multiagent systems it is typical that agents share incomplete information with each other, otherwise multiagent systems will degenerate to systems with a single agent. The incompleteness of information is normally characterized by defining for each agent an equivalence relation over all global states of the systems; two global states are considered indistinguishable for a given agent if they are related by the equivalence relation. Two states that are indistinguishable for an agent may be distinguishable for another agent. It is a natural, and realistic, setting that every agent makes its own decisions based only on the limited information it has; namely, the information provided by its own indistinguishability relation, and nothing else. Decisions of agents are usually formalized by schedulers (also known as policies or strategies), which are functions taking history executions as input and deciding the next move for each agent. Schedulers only making use of limited information of each agent are called uniform (or decentralized).


This tool is used to model check Probabilistic Epistemic Temporal Logic (PETL) for Probabilistic Multiagent Systems. For more information about the algorithms, please visit https://www.ijcai.org/proceedings/2018/661.


## About the files
This tool is implemented as a plugin in ePMC. All the implementation details related to PETL model checking are under "epmc-petl/plugins/propertysolver-petl". 

You can find the experiment files used in the paper under "experiment_files". 

## Building and running

For building, running and other information about ePMC, please visit https://github.com/ISCAS-PMC/ePMC. The easiest way is to firstly build the project by command line './build.sh petl' and then use 'epmc-petl.jar'.

There are two algorithms for PETL model checking, to run the algorithm which reduces the problem to MINLP, you need to set the following options:
```
--property-solver propositional-explicit,operator-explicit,pctl-explicit-next,petl-explicit-knowledge,petl-until-minlp
--prism-flatten false
--model-input-type mas
--property-input-type petl
--smtlib-command-line z3 -smt2 {0} 
--smtlib-version v25 
--constraintsolver-solver smt-lib-petl
--model-input-files /path/to/your-model /path/to/your-equivalence-relation 
--property-input-files /path/to/your-property
```

To run the algorithm based on UCT, you need to set the following options:
```
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

You need to prepare 3 files: one for the model, one for equivalence relations, and one for properties.

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

## Tips for developing

Although there is  a "epmc-constraintsolver-smt-lib" plugin, it's not enough for our MINLP problems. We change the classes "ConstraintSolverSMTLib", "InputWriter", and "OutputReader". And we  also copy "SMTLibOperator", "SMTLibResult", and "SMTLibVariable", because they are not public classes.  We use some other classes from  "epmc-constraintsolver-smt-lib", so  we need to add this plugin as a dependency. We call our new constraint solver as "smt-lib-petl".


"ModelMAS" is the class to store the model, where we change the composition of the modules. And "EquivalenceRelations" is the class for  equivalence relations.


The model checking algorithms are in the classes under epmc.propertysolver in the petl plugin.

## Contact
Comments and feedback about any this project are very welcome. Please contact:

Chen Fu

fchen###ios.ac.cn

