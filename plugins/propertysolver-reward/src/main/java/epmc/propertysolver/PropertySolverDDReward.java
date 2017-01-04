package epmc.propertysolver;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

import epmc.error.EPMCException;
import epmc.expression.Expression;
import epmc.expression.standard.CmpType;
import epmc.expression.standard.DirType;
import epmc.expression.standard.ExpressionQuantifier;
import epmc.expression.standard.ExpressionReward;
import epmc.expression.standard.evaluatordd.ExpressionToDD;
import epmc.graph.CommonProperties;
import epmc.graph.StateMap;
import epmc.graph.StateMapDD;
import epmc.graph.StateSet;
import epmc.graph.UtilGraph;
import epmc.graph.dd.GraphDD;
import epmc.modelchecker.EngineDD;
import epmc.modelchecker.ModelChecker;
import epmc.modelchecker.PropertySolver;
import epmc.value.ContextValue;
import epmc.value.Operator;

// TODO check whether this works for JANI MDPs - probably not
// TODO transform to DD checker

public final class PropertySolverDDReward implements PropertySolver {
    public final static String IDENTIFIER = "reward-dd";
    private ModelChecker modelChecker;
    private GraphDD graph;
    private ContextValue contextValue;
	private Expression property;
	private ExpressionQuantifier propertyQuantifier;
	private StateSet forStates;

    @Override
    public void setModelChecker(ModelChecker modelChecker) {
        assert modelChecker != null;
        this.modelChecker = modelChecker;
        if (modelChecker.getEngine() instanceof EngineDD) {
        	this.graph = modelChecker.getLowLevel();
        }
        this.contextValue = modelChecker.getModel().getContextValue();
    }

	@Override
	public void setProperty(Expression property) {
		this.property = property;
		if (property instanceof ExpressionQuantifier) {
			this.propertyQuantifier = (ExpressionQuantifier) property;
		}
	}

	@Override
	public void setForStates(StateSet forStates) {
		this.forStates = forStates;
	}

	@Override
	public Set<Object> getRequiredGraphProperties() throws EPMCException {
		Set<Object> required = new LinkedHashSet<>();
		required.add(CommonProperties.EXPRESSION_TO_DD);
		return Collections.unmodifiableSet(required);
	}

	@Override
	public Set<Object> getRequiredNodeProperties() throws EPMCException {
		return Collections.emptySet();
	}

	@Override
	public Set<Object> getRequiredEdgeProperties() throws EPMCException {
		return Collections.emptySet();
	}

    @Override
    public StateMap solve() throws EPMCException {
        ExpressionReward quantifiedProp = (ExpressionReward) propertyQuantifier.getQuantified();
        if (quantifiedProp.getRewardType().isReachability()) {
        	StateSet allStates = UtilGraph.computeAllStatesDD(modelChecker.getLowLevel());
        	Expression reachSet = ((ExpressionReward) (propertyQuantifier.getQuantified())).getRewardReachSet();
        	StateMapDD innerResult = (StateMapDD) modelChecker.check(reachSet, allStates);
            ExpressionToDD expressionToDD = graph
                    .getGraphPropertyObject(CommonProperties.EXPRESSION_TO_DD);
            expressionToDD.putConstantWith(reachSet, innerResult.getValuesDD());
            allStates.close();
        }
        DirType dirType = ExpressionQuantifier.computeQuantifierDirType(propertyQuantifier);
        boolean min = dirType == DirType.MIN;
//        StateMap result = doSolve(quantifiedProp, forStates, min);
        if (propertyQuantifier.getCompareType() != CmpType.IS) {
            StateMap compare = modelChecker.check(propertyQuantifier.getCompare(), forStates);
            Operator op = propertyQuantifier.getCompareType().asExOpType(contextValue);
//            result = result.applyWith(op, compare);
        }
  //      return result;
		return null;
    }


    @Override
    public boolean canHandle() throws EPMCException {
        assert property != null;
        assert forStates != null;
        if (!(modelChecker.getEngine() instanceof EngineDD)) {
            return false;
        }
        if (!(property instanceof ExpressionQuantifier)) {
            return false;
        }
        if (!(propertyQuantifier.getQuantified() instanceof ExpressionReward)) {
            return false;
        }
        StateSet allStates = UtilGraph.computeAllStatesDD(modelChecker.getLowLevel());
        if (((ExpressionReward) (propertyQuantifier.getQuantified())).getRewardType().isReachability()) {
        	modelChecker.ensureCanHandle(((ExpressionReward) (propertyQuantifier.getQuantified())).getRewardReachSet(), allStates);
        }
        allStates.close();
        return true;
    }

    @Override
    public String getIdentifier() {
        return IDENTIFIER;
    }
}
