## Model Checking Probabilistic Epistemic Logic for Probabilistic Multiagent Systems

This tool is implemented as a plugin in ePMC. For building, running and other information about ePMC, please visit https://github.com/liyi-david/ePMC.

To perform PETL model checking, you need to prepare 3 files: one for the model, one for equivalence relations, and one for properties.

The input models are described using the PRISM language(http://www.prismmodelchecker.org/manual/ThePRISMLanguage/Introduction). Note that we redefine the composition of the modules to make the agents all take one local action in each transition, so the transitions from different modules will not synchronize according to the parallel composition operator.

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
Other properties are described using the PRISM property specification language(http://www.prismmodelchecker.org/manual/PropertySpecification/Introduction).
