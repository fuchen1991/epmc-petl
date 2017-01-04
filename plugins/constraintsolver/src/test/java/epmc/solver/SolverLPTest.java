package epmc.solver;


import static epmc.modelchecker.TestHelper.assertEquals;
import static epmc.modelchecker.TestHelper.prepare;
import static epmc.modelchecker.TestHelper.prepareOptions;
import static epmc.value.UtilValue.newValue;

import org.junit.BeforeClass;
import org.junit.Test;

import epmc.constraintsolver.ConstraintSolver;
import epmc.constraintsolver.ConstraintSolverConfiguration;
import epmc.constraintsolver.ConstraintType;
import epmc.constraintsolver.Direction;
import epmc.constraintsolver.Feature;
import epmc.error.EPMCException;
import epmc.modelchecker.TestHelper;
import epmc.options.Options;
import epmc.value.ContextValue;
import epmc.value.TypeReal;
import epmc.value.Value;
import epmc.value.ValueArray;

public class SolverLPTest {
    
    @BeforeClass
    public static void initialise() {
        prepare();
    }

    @Test
    public void wikipediaTest() throws EPMCException {
        final double tolerance = 1E-10;
        Options options = prepareOptions();
        ContextValue contextValue = options.get(TestHelper.CONTEXT_VALUE);
        options.set(TestHelper.CONTEXT_VALUE, contextValue);
        ConstraintSolverConfiguration contextSolver = new ConstraintSolverConfiguration(contextValue);
        contextSolver.requireFeature(Feature.LP);
        ConstraintSolver problem = contextSolver.newProblem();
        problem.setDirection(Direction.MAX);
        int x = problem.addVariable("x", TypeReal.get(contextValue));
        int y = problem.addVariable("y", TypeReal.get(contextValue));
        TypeReal typeReal = TypeReal.get(contextValue);
        int[] variables = new int[]{x, y};
        
        problem.setObjective(new Value[]{newValue(typeReal, 300), newValue(typeReal, 500)},
                variables);
        problem.addConstraint(new Value[]{newValue(typeReal, 1), newValue(typeReal, 2)}, variables,
        ConstraintType.LE, newValue(typeReal, 170));
        problem.addConstraint(new Value[]{newValue(typeReal, 1), newValue(typeReal, 1)}, variables,
        ConstraintType.LE, newValue(typeReal, 150));
        problem.addConstraint(new Value[]{newValue(typeReal, 0), newValue(typeReal, 3)}, variables,
        ConstraintType.LE, newValue(typeReal, 180));
        problem.solve();
        Value optimalValue = problem.getResultObjectiveValue();
        ValueArray optimalVariables = problem.getResultVariablesValuesSingleType();
        assertEquals(49000, optimalValue, tolerance);
        Value entry = typeReal.newValue();
        optimalVariables.get(entry, x);
        assertEquals(130, entry, tolerance);
        optimalVariables.get(entry, y);
        assertEquals(20, entry, tolerance);
    }
}
