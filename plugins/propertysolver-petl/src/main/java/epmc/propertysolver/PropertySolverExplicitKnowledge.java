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

package epmc.propertysolver;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import epmc.expression.Expression;
import epmc.expression.standard.evaluatorexplicit.EvaluatorExplicitBoolean;
import epmc.expression.standard.evaluatorexplicit.UtilEvaluatorExplicit;
import epmc.graph.CommonProperties;
import epmc.graph.Semantics;
import epmc.graph.SemanticsDTMC;
import epmc.graph.SemanticsMDP;
import epmc.graph.StateMap;
import epmc.graph.StateSet;
import epmc.graph.UtilGraph;
import epmc.graph.explicit.GraphExplicit;
import epmc.graph.explicit.StateMapExplicit;
import epmc.graph.explicit.StateSetExplicit;
import epmc.modelchecker.EngineExplicit;
import epmc.modelchecker.ModelChecker;
import epmc.modelchecker.PropertySolver;
import epmc.petl.model.ExpressionKnowledge;
import epmc.prism.model.ModelMAS;
import epmc.util.BitSet;
import epmc.util.UtilBitSet;
import epmc.value.Type;
import epmc.value.UtilValue;
import epmc.value.Value;
import epmc.value.ValueArray;
import epmc.value.ValueBoolean;

/**
 * This class implements a propertysolver which uses an explicit graph data structure
 * to check the knowledge properties in a MDP.
 * 
 * @author Chen Fu
 */


public class PropertySolverExplicitKnowledge implements PropertySolver {
	public final static String IDENTIFIER = "petl-explicit-knowledge";
	private ModelChecker modelChecker;
    private GraphExplicit graph;
    private Expression property;
    private StateSet forStates;
    
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
        if (!(property instanceof ExpressionKnowledge)) {
            return false;
        }
        return true;
	}

	@Override
	public StateMap solve() {
		assert property != null;
        assert forStates != null;
        assert property instanceof ExpressionKnowledge;
        
        StateSetExplicit forStatesExplicit = (StateSetExplicit) forStates;
        graph.explore(forStatesExplicit.getStatesExplicit());
        ExpressionKnowledge propertyKnowledge = (ExpressionKnowledge) property;
        Expression quantifier = propertyKnowledge.getQuantifier();

        StateSet allStates = UtilGraph.computeAllStatesExplicit(modelChecker.getLowLevel());
        StateMapExplicit innerResult = (StateMapExplicit) modelChecker.check(quantifier, allStates);
        UtilGraph.registerResult(graph, quantifier, innerResult);
        allStates.close();

        EvaluatorExplicitBoolean evaluator = UtilEvaluatorExplicit.newEvaluatorBoolean(quantifier, graph, quantifier);
        Value evalValues = innerResult.getType().newValue();
        
        int NodeNum = graph.getNumNodes();
        BitSet oneStates = UtilBitSet.newBitSetBounded(NodeNum);
        for (int node = 0; node < NodeNum; node ++) {
            evalValues = graph.getNodeProperty(quantifier).get(node);
            evaluator.setValues(evalValues);
            boolean sat = evaluator.evaluateBoolean();
            if (sat)  
            	oneStates.set(node);
        }

        BitSet res = UtilBitSet.newBitSetBounded(NodeNum);
        BitSet helper = UtilBitSet.newBitSetBounded(NodeNum);
        int forStateSize = forStates.size();
        for(int stateNr=0;stateNr<forStateSize;stateNr++)
        {
        	int state = forStatesExplicit.getExplicitIthState(stateNr);
        	if(helper.get(state))
        		continue;
        	
        	BitSet equiv = UtilPETL.getEquivalenceClass(state, property, modelChecker);

        	if(UtilPETL.isSubsetOf(equiv, oneStates)) 
        	{
        		for(int i = equiv.nextSetBit(0);i>=0;i=equiv.nextSetBit(i+1))
            	{
            		if(forStatesExplicit.isExplicitContains(i))
            			res.set(i);
            	}
        	}
        	helper.and(equiv);
        }
        
        Type type = evaluator.getType();
        ValueArray resultValues = UtilValue.newArray(type.getTypeArray(), forStates.size());
        for (int stateNr = 0; stateNr < forStateSize; stateNr++) {
            int state = forStatesExplicit.getExplicitIthState(stateNr);
            ValueBoolean value = (ValueBoolean) type.newValue();
            if(res.get(state))
            	value.set(true);
            else
            	value.set(false);

            resultValues.set(value, stateNr);
        }
		
		return UtilGraph.newStateMap(forStatesExplicit.clone(), resultValues);
	}
	
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

        ExpressionKnowledge propertyKnowledge = (ExpressionKnowledge) property;
        Set<Expression> inners = new LinkedHashSet<>();
        inners.addAll(UtilPETL.collectPETLInner(propertyKnowledge.getQuantifier()));
        Collection<List<Expression>> lists = ((ModelMAS) this.modelChecker.getModel()).getEquivalenceRelations().getEquivalenceRelations().values();
        for(List<Expression> list : lists)
        {
        	inners.addAll(list);
        }
        StateSet allStates = UtilGraph.computeAllStatesExplicit(modelChecker.getLowLevel());
        for (Expression inner : inners) {
            required.addAll(modelChecker.getRequiredNodeProperties(inner, allStates));
        }
        return required;
	}

	@Override
	public Set<Object> getRequiredEdgeProperties() {
		Set<Object> required = new LinkedHashSet<>();
        required.add(CommonProperties.WEIGHT);
        return required;
	}

}
