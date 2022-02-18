package epmc.propertysolver;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

import epmc.expression.Expression;
import epmc.expression.standard.CmpType;
import epmc.expression.standard.DirType;
import epmc.expression.standard.ExpressionQuantifier;
import epmc.expression.standard.ExpressionReward;
import epmc.expression.standard.ExpressionTemporalUntil;
import epmc.expression.standard.RewardSpecification;
import epmc.expression.standard.RewardType;
import epmc.expression.standard.evaluatorexplicit.UtilEvaluatorExplicit;
import epmc.graph.CommonProperties;
import epmc.graph.Semantics;
import epmc.graph.SemanticsDTMC;
import epmc.graph.SemanticsMDP;
import epmc.graph.StateMap;
import epmc.graph.StateSet;
import epmc.graph.UtilGraph;
import epmc.graph.explicit.EdgeProperty;
import epmc.graph.explicit.GraphExplicit;
import epmc.graph.explicit.NodeProperty;
import epmc.graph.explicit.StateMapExplicit;
import epmc.graph.explicit.StateSetExplicit;
import epmc.jani.model.Action;
import epmc.modelchecker.EngineExplicit;
import epmc.modelchecker.ModelChecker;
import epmc.modelchecker.PropertySolver;
import epmc.operator.Operator;
import epmc.petl.model.ModelMAS;
import epmc.util.BitSet;
import epmc.util.UtilBitSet;
import epmc.value.Type;
import epmc.value.TypeBoolean;
import epmc.value.TypeDouble;
import epmc.value.UtilValue;
import epmc.value.Value;
import epmc.value.ValueArray;
import epmc.value.ValueBoolean;
import epmc.value.ValueDouble;
import epmc.value.ValueInteger;


public class PropertySolverPOSGReachReward implements PropertySolver{
	public final static String IDENTIFIER = "posg-reach-reward";
	private ModelChecker modelChecker;
    private GraphExplicit graph;
    private StateSetExplicit computeForStates;
    private Expression property;
    private StateSet forStates;
    static long maxMemoryUsage =  0;
	@Override
	public String getIdentifier() {
		return IDENTIFIER;
	}

	@Override
	public void setModelChecker(ModelChecker modelChecker) {
		assert modelChecker != null;
        this.modelChecker = modelChecker;
        if (modelChecker.getEngine() instanceof EngineExplicit) {
            this.graph = modelChecker.getLowLevel();
        }
	}

	@Override
	public void setProperty(Expression property) {
		this.property = property;
		
	}

	@Override
	public void setForStates(StateSet forStates) {
		this.forStates = forStates;
		
	}

	@Override
	public boolean canHandle() {
		assert property != null;
        if (!(modelChecker.getEngine() instanceof EngineExplicit)) {
            return false;
        }
        Semantics semantics = modelChecker.getModel().getSemantics();
        if (!SemanticsDTMC.isDTMC(semantics) && !SemanticsMDP.isMDP(semantics)) {
            return false;
        }
        
        if (!(property instanceof ExpressionQuantifier)) {
            return false;
        } 

        if (!(modelChecker.getModel() instanceof ModelMAS)) {
            return false;
        }
        
        
        ExpressionQuantifier propertyQuantifier = (ExpressionQuantifier) property;
        if (!(propertyQuantifier.getQuantified() instanceof ExpressionReward)) {
            return false;
        }
        ExpressionReward quantifiedReward = (ExpressionReward) propertyQuantifier.getQuantified();
        if (quantifiedReward.getRewardType() != RewardType.REACHABILITY) {
            return false;
        }
        return true;
	}

	@Override
	public Set<Object> getRequiredGraphProperties() {
		Set<Object> required = new LinkedHashSet<>();
        required.add(CommonProperties.SEMANTICS);
        return required;
	}

	@Override
	public Set<Object> getRequiredNodeProperties() {
		Set<Object> required = new LinkedHashSet<>();
        required.add(CommonProperties.STATE);
        required.add(CommonProperties.PLAYER);
        ExpressionQuantifier propertyQuantifier = (ExpressionQuantifier) property;
        ExpressionReward quantifiedReward = (ExpressionReward) propertyQuantifier.getQuantified();
        required.add(quantifiedReward.getReward());
        RewardType rewardType = quantifiedReward.getRewardType();
        if (rewardType.isReachability()) {
            required.addAll(modelChecker.getRequiredNodeProperties(quantifiedReward.getRewardReachSet(), forStates));
        }
        
        StateSet allStates = UtilGraph.computeAllStatesExplicit(modelChecker.getLowLevel());
        Set<Expression> expOfEquiv = ((ModelMAS) modelChecker.getModel()).getEquivalenceRelations().getAllExpressions();
        for (Expression inner : expOfEquiv) {
            required.addAll(modelChecker.getRequiredNodeProperties(inner, allStates));
        }
        
        return Collections.unmodifiableSet(required);
	}

	@Override
	public Set<Object> getRequiredEdgeProperties() {
		Set<Object> required = new LinkedHashSet<>();
        required.add(CommonProperties.WEIGHT);
        required.add(CommonProperties.TRANSITION_LABEL);
        ExpressionQuantifier propertyQuantifier = (ExpressionQuantifier) property;
        required.add(((ExpressionReward) (propertyQuantifier.getQuantified())).getReward());
        return Collections.unmodifiableSet(required);
	}

	@Override
	public StateMap solve() {
		assert property != null;
        assert forStates != null;
        assert property instanceof ExpressionQuantifier;
		
        countMemoryUsage();
        
        ExpressionQuantifier propertyQuantifier = (ExpressionQuantifier) property;
        ExpressionReward quantifiedProp = (ExpressionReward) propertyQuantifier.getQuantified();
        DirType dirType = ExpressionQuantifier.computeQuantifierDirType(propertyQuantifier);
        boolean min = dirType == DirType.MIN;
  
        countMemoryUsage();
        StateMap result = doSolve(quantifiedProp, (StateSetExplicit) forStates, min);
        
        countMemoryUsage();
        if (propertyQuantifier.getCompareType() != CmpType.IS) {
            StateMap compare = modelChecker.check(propertyQuantifier.getCompare(), forStates);
            Operator op = propertyQuantifier.getCompareType().asExOpType();
            result = result.applyWith(op, compare);
        }
        
        System.out.println("Max memory usage:" + maxMemoryUsage + " MB");
        return result;
	}

	public StateMap doSolve(Expression property, StateSetExplicit states, boolean min)
	{
		this.computeForStates = (StateSetExplicit) states;
		ExpressionReward propertyReward = (ExpressionReward) property;

		StateSet allStates = UtilGraph.computeAllStatesExplicit(modelChecker.getLowLevel());
        Expression op = propertyReward.getChildren().get(1);
        StateMapExplicit innerResult = (StateMapExplicit) modelChecker.check(op, allStates);
        UtilGraph.registerResult(graph, op, innerResult);
        allStates.close();
        
        BitSet canNotReachSet = UtilBitSet.newBitSetUnbounded();
        BitSet reachSet = UtilBitSet.newBitSetUnbounded();
        NodeProperty stateProp = graph.getNodeProperty(CommonProperties.STATE);
        ValueBoolean valueInner = TypeBoolean.get().newValue();
        
        for (int i = 0; i < innerResult.size(); i++) {
            int state = innerResult.getExplicitIthState(i);
            if (!stateProp.getBoolean(state)) {
                continue;
            }
            innerResult.getExplicitIthValue(valueInner, i);
            boolean inner = valueInner.getBoolean();
            if(inner)
            {
            	reachSet.set(state);
            }
        }
        
        BitSet unKnown = UtilPETL.getUnKnownStates(reachSet, canNotReachSet, graph);

		RewardSpecification rewardStructure = ((ExpressionReward) property).getReward();
        NodeProperty stateReward = graph.getNodeProperty(rewardStructure);
        EdgeProperty transReward = graph.getEdgeProperty(rewardStructure);

        countMemoryUsage();
        double[] resultValue = UtilReachReward.computeProbabilities(unKnown, reachSet, canNotReachSet, min,computeForStates, graph,modelChecker,stateReward, transReward);

		Type type = TypeDouble.get();
        ValueArray resultValues = UtilValue.newArray(type.getTypeArray(), computeForStates.size());
        for (int stateNr = 0; stateNr < computeForStates.size(); stateNr++) {
            ValueDouble value = (ValueDouble) type.newValue();
            value.set(resultValue[stateNr]);
            resultValues.set(value, stateNr);
        }
		return UtilGraph.newStateMap(computeForStates.clone(), resultValues);
	}
	
	static void countMemoryUsage() {
    	long curr = (Runtime.getRuntime().totalMemory()-Runtime.getRuntime().freeMemory())/1024/1024;
    	if(curr > maxMemoryUsage)
    		maxMemoryUsage = curr;
    }
}
