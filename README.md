# Model Checking Probabilistic Multiagent Systems under Uniform Schedulers

## Introduction
Multiagent systems have found many applications in practice. We focus on probabilistic multiagent systems which can model uncertainty, such as component failure, of the agents and/or their environment. In multiagent systems it is typical that agents share incomplete information with each other, otherwise multiagent systems will degenerate to systems with a single agent. The incompleteness of information is normally characterized by defining for each agent an equivalence relation over all global states of the systems; two global states are considered indistinguishable for a given agent if they are related by the equivalence relation. Two states that are indistinguishable for an agent may be distinguishable for another agent. It is a natural, and realistic, setting that every agent makes its own decisions based only on the limited information it has; namely, the information provided by its own indistinguishability relation, and nothing else. Decisions of agents are usually formalized by schedulers (also known as policies or strategies), which are functions taking history executions as input and deciding the next move for each agent. Schedulers only making use of limited information of each agent are called uniform (or decentralized).


This tool is used to model check Probabilistic Epistemic Temporal Logic (PETL) for Probabilistic Multiagent Systems. For more information about the algorithms, please visit https://www.ijcai.org/proceedings/2018/661.


## About the files
This tool is implemented as a plugin in ePMC. Almost all the implementation details related to PETL model checking are under "epmc-petl/plugins/propertysolver-petl". The only exception is in plugins/constraintsolver-smt-lib/src/main/java/epmc/constraintsolver/smtlib/ConstraintSolverSMTLib.java, where we add these lines:
```java
public int getNumberOfVariables()
	{
		return this.variables.size();
	}
	public int getNumberOfConstraints()
	{
		//For each variable, we need to add two more constraints
		return this.constraints.size() + 2*this.variables.size();
	}
```
to get the numbers of variables and constraints in the MINLP problems. This doesn't affect the algorithms, so if you don't want this or just don't want to add the above code, you can comment this two lines:
```java
System.out.println("Number of variables:" + ((ConstraintSolverSMTLib)solver).getNumberOfVariables());
System.out.println("Number of constraints:" + ((ConstraintSolverSMTLib)solver).getNumberOfConstraints());
```
in function 'computeProbabilities' at plugins/propertysolver-petl/src/main/java/epmc/propertysolver/UtilConstraints.java.

You can find the experiment files used in the paper under "experiment_files". 

## Building and running

For building, running and other information about ePMC, please visit https://github.com/ISCAS-PMC/ePMC. Note that the easiest way is to run command line './build.sh petl' and use 'epmc-petl.jar'.

To perform PETL model checking, please set the following options:
```
--property-solver propositional-explicit,operator-explicit,pctl-explicit-next,petl-explicit-knowledge,pctl-explicit-until-uniform
--prism-flatten false
--model-input-type mas
--property-input-type petl
--smtlib-command-line z3 -smt2 {0} 
--smtlib-version v25 
--constraintsolver-solver smt-lib 
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

## Contact
Comments and feedback about any this project are very welcome. Please contact:

Chen Fu

fchen###ios.ac.cn
