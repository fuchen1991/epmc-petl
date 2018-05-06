# EPMC - (An Extendible Probabilistic Model Checker, previously known as IscasMC)

The code for model checking PETL on MAS is implemented in EPMC. For more information about EPMC, please see https://github.com/liyi-david/ePMC.

To perform our tool, you need three files: one for model, one for equivalence relations, and one for properties.

The input models are described using the PRISM language. Note that we redefine the composition of the modules to make the agents all take one action in each transition (independently on its action), so the transitions from different modules will not synchronize according to the parallel composition operator.

The equivalence relations are described like this:
==============================
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
==============================
Each agent in the model has a "equiv (agent name) ... equiv end" block, and there are formulas in it. You can use the variables used in the model. All the states satisfying the same formula are regarded as equivalent by the agent. So you can not write formulas such that one state satisfies two or more formulas. If one state can not satisfy any formula, it's not equivalent to any other states.

The knowledge properties are described like this:
K {agent}  (state_formula)
E/C/D {agent1,..., agentn}  (state_formula)
Other properties are described using the PRISM property specification language.

