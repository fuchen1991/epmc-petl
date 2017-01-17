/****************************************************************************

    ePMC - an extensible probabilistic model checker
    Copyright (C) 2017

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.

*****************************************************************************/

package epmc.multiobjective;

import static epmc.error.UtilError.ensure;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

import epmc.error.EPMCException;
import epmc.expression.Expression;
import epmc.expression.standard.ExpressionMultiObjective;
import epmc.expression.standard.ExpressionQuantifier;
import epmc.expression.standard.ExpressionReward;
import epmc.graph.CommonProperties;
import epmc.graph.StateMap;
import epmc.graph.StateSet;
import epmc.graph.UtilGraph;
import epmc.graph.explicit.GraphExplicit;
import epmc.graph.explicit.StateMapExplicit;
import epmc.graph.explicit.StateSetExplicit;
import epmc.modelchecker.EngineExplicit;
import epmc.modelchecker.ModelChecker;
import epmc.modelchecker.PropertySolver;
import epmc.util.BitSet;
import epmc.value.ContextValue;
import epmc.value.TypeArray;
import epmc.value.TypeBoolean;
import epmc.value.TypeWeight;
import epmc.value.UtilValue;
import epmc.value.Value;
import epmc.value.ValueAlgebra;
import epmc.value.ValueArray;
import epmc.value.ValueArrayAlgebra;
import epmc.value.ValueBoolean;

public final class PropertySolverExplicitMultiObjective implements PropertySolver {
    public final static String IDENTIFIER = "multiobjective-explicit";

    private ModelChecker modelChecker;
	private Expression property;
	private ExpressionMultiObjective propertyMultiObjective;
	private StateSet forStates;
    
    @Override
	public String getIdentifier() {
	    return IDENTIFIER;
	}

	@Override
    public void setModelChecker(ModelChecker modelChecker) {
        assert modelChecker != null;
        this.modelChecker = modelChecker;
    }

	@Override
	public void setProperty(Expression property) {
		this.property = property;
		if (property instanceof ExpressionMultiObjective) {
			this.propertyMultiObjective = (ExpressionMultiObjective) property;
		}
	}

	@Override
	public void setForStates(StateSet forStates) {
		this.forStates = forStates;
	}

    @Override
	public boolean canHandle() throws EPMCException {
	    assert property != null;
	    if (!(modelChecker.getEngine() instanceof EngineExplicit)) {
	        return false;
	    }
	    if (!(property instanceof ExpressionMultiObjective)) {
	        return false;
	    }
	    StateSet allStates = UtilGraph.computeAllStatesExplicit(modelChecker.getLowLevel());
	    for (Expression objective : propertyMultiObjective.getOperands()) {
        	ExpressionQuantifier objectiveQuantifier = (ExpressionQuantifier) objective;
	        Set<Expression> inners = UtilLTL.collectLTLInner(objectiveQuantifier.getQuantified());
	        for (Expression inner : inners) {
	            modelChecker.ensureCanHandle(inner, allStates);
	        }
	    }
	    if (allStates != null) {
	    	allStates.close();
	    }
	    return true;
	}

	@Override
	public Set<Object> getRequiredGraphProperties() throws EPMCException {
		Set<Object> required = new LinkedHashSet<>();
		required.add(CommonProperties.SEMANTICS);
		return Collections.unmodifiableSet(required);
	}

	@Override
	public Set<Object> getRequiredNodeProperties() throws EPMCException {
		Set<Object> required = new LinkedHashSet<>();
		required.add(CommonProperties.STATE);
		required.add(CommonProperties.PLAYER);
	    for (Expression objective : propertyMultiObjective.getOperands()) {
	    	ExpressionQuantifier objectiveQuantifier = (ExpressionQuantifier) objective;
	        Expression quantified = objectiveQuantifier.getQuantified();
	        if (quantified instanceof ExpressionReward) {
	            required.add(((ExpressionReward) quantified).getReward());
	        } else {
	        	for (Expression inner : UtilLTL.collectLTLInner(quantified)) {
	            	required.addAll(modelChecker.getRequiredNodeProperties(inner, forStates));
	        	}
	        }
	    }
		return Collections.unmodifiableSet(required);
	}

	@Override
	public Set<Object> getRequiredEdgeProperties() throws EPMCException {
		Set<Object> required = new LinkedHashSet<>();
		required.add(CommonProperties.WEIGHT);
	    for (Expression objective : propertyMultiObjective.getOperands()) {
        	ExpressionQuantifier objectiveQuantifier = (ExpressionQuantifier) objective;
	        Expression quantified = objectiveQuantifier.getQuantified();
	        if (quantified instanceof ExpressionReward) {
	            required.add(((ExpressionReward) quantified).getReward());
	        }
	    }
		return Collections.unmodifiableSet(required);
	}

	@Override
    public StateMap solve() throws EPMCException {
        assert property != null;
        assert forStates != null;
        StateSetExplicit initialStates = (StateSetExplicit) modelChecker.getLowLevel().newInitialStateSet();
        ensure(initialStates.size() == 1, ProblemsMultiObjective.MULTI_OBJECTIVE_INITIAL_NOT_SINGLETON);
        PropertyNormaliser normaliser = new PropertyNormaliser()
        		.setOriginalProperty(propertyMultiObjective)
        		.setExpressionToType(modelChecker.getLowLevel())
        		.build();
        property = propertyMultiObjective = normaliser.getNormalisedProperty();
        Value subtractNumericalFrom = normaliser.getSubtractNumericalFrom();
        BitSet invertedRewards = normaliser.getInvertedRewards();
        prepareRequiredPropositionals();
    	GraphExplicit graph = modelChecker.getLowLevel();
        Product product = new ProductBuilder()
        		.setProperty(propertyMultiObjective)
        		.setModelChecker(modelChecker)
        		.setGraph(graph)
        		.setInvertedRewards(invertedRewards)
        		.build();
        return mainLoop(product, subtractNumericalFrom);
    }

    /**
	 * Compute values of required propositional properties and register their values.
	 * 
	 * @throws EPMCException thrown in case of problems during computation
	 */
	private void prepareRequiredPropositionals() throws EPMCException {
		GraphExplicit graph = modelChecker.getLowLevel();
	    StateSet allStates = UtilGraph.computeAllStatesExplicit(modelChecker.getLowLevel());
	    for (Expression objective : propertyMultiObjective.getOperands()) {
	    	ExpressionQuantifier objectiveQuantifier = (ExpressionQuantifier) objective;
	        Expression quantified = objectiveQuantifier.getQuantified();
	        Set<Expression> inners = UtilLTL.collectLTLInner(quantified);
	        for (Expression inner : inners) {
	            StateMapExplicit innerResult = (StateMapExplicit) modelChecker.check(inner, allStates);
	            UtilGraph.registerResult(graph, inner, innerResult);
	        }
	    }
	    allStates.close();
	}

	private StateMap mainLoop(Product product, Value subtractNumericalFrom) throws EPMCException {
    	assert product != null;
        GraphExplicit iterGraph = product.getGraph();
        MultiObjectiveIterationRewards combinations = product.getRewards();
        ValueArrayAlgebra bounds = MultiObjectiveUtils.computeQuantifierBoundsArray(modelChecker, propertyMultiObjective, !ValueAlgebra.asAlgebra(subtractNumericalFrom).isPosInf());
        int numAutomata = product.getNumAutomata();
        MultiObjectiveDownClosure down = new MultiObjectiveDownClosure(getContextValue(), numAutomata);
        ValueArrayAlgebra weights;
        boolean feasible = false;
        boolean numerical = MultiObjectiveUtils.isNumericalQuery(propertyMultiObjective);
        do {
            weights = down.findSeparating(bounds, numerical);
            if (weights == null) {
                feasible = true;
                break;
            }
            ValueArrayAlgebra q = newValueArrayWeight(numAutomata);
            MultiObjectiveUtils.iterate(q, weights, iterGraph, combinations);
            if (MultiObjectiveUtils.compareProductDistance(weights, q, bounds) < 0) {
                feasible = false;
                break;
            }
            down.add(q);
            if (numerical) {
                down.improveNumerical(bounds);
                if (MultiObjectiveUtils.compareProductDistance(weights, q, bounds) <= 0) {
                    feasible = true;
                    break;
                }
            }
        } while (true);
        return prepareResult(numerical, feasible, bounds, subtractNumericalFrom);
	}

	private StateMap prepareResult(boolean numerical, boolean feasible, ValueArray bounds, Value subtractNumericalFrom)
			throws EPMCException {
        ValueArray resultValues;
        if (numerical) {
            ensure(feasible, ProblemsMultiObjective.MULTI_OBJECTIVE_UNEXPECTED_INFEASIBLE);
            resultValues = newValueArrayWeight(forStates.size());
            ValueAlgebra entry = newValueWeight();
            bounds.get(entry, 0);
            if (!ValueAlgebra.asAlgebra(subtractNumericalFrom).isPosInf()) {
                entry.subtract(subtractNumericalFrom, entry);
            }
            for (int i = 0; i < forStates.size(); i++) {
                resultValues.set(entry, i);
            }
        } else {
            resultValues = UtilValue.newArray(TypeBoolean.get(getContextValue()).getTypeArray(),
            		forStates.size());
            ValueBoolean valueFeasible = TypeBoolean.get(getContextValue()).newValue();
            valueFeasible.set(feasible);
            for (int i = 0; i < forStates.size(); i++) {
                resultValues.set(valueFeasible, i);
            }
        }
        return UtilGraph.newStateMap((StateSetExplicit) forStates.clone(), resultValues);
	}

	private ContextValue getContextValue() {
    	return modelChecker.getModel().getContextValue();
    }
    
    private ValueArrayAlgebra newValueArrayWeight(int size) {
        TypeArray typeArray = TypeWeight.get(getContextValue()).getTypeArray();
        return UtilValue.newArray(typeArray, size);
    }
    
    private ValueAlgebra newValueWeight() {
    	return TypeWeight.get(getContextValue()).newValue();
    }
}