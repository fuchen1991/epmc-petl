package epmc.petl.model;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import epmc.expression.Expression;
import epmc.expression.standard.evaluatorexplicit.EvaluatorExplicitBoolean;
import epmc.expression.standard.evaluatorexplicit.UtilEvaluatorExplicit;
import epmc.graph.CommonProperties;
import epmc.graph.StateSet;
import epmc.graph.UtilGraph;
import epmc.graph.explicit.GraphExplicit;
import epmc.graph.explicit.NodeProperty;
import epmc.graph.explicit.StateMapExplicit;
import epmc.modelchecker.ModelChecker;
import epmc.propertysolver.UtilPETL;
import epmc.util.BitSet;
import epmc.util.UtilBitSet;
import epmc.value.Value;

public class EquivalenceClasses {
	private Map<String, Map<Integer, BitSet>> equivalenceClassesMap;
	private Map<String, List<BitSet>>  equivalenceClasses;
	
	public EquivalenceClasses(ModelChecker modelChecker)
	{
		assert modelChecker != null;

		EquivalenceRelations relations = ((ModelMAS) modelChecker.getModel()).getEquivalenceRelations();
		
		GraphExplicit graph = modelChecker.getLowLevel();
		equivalenceClassesMap = new HashMap<String, Map<Integer, BitSet>>();
		equivalenceClasses = new HashMap<String, List<BitSet>>();
		Map<String, List<Expression>> rel = relations.getEquivalenceRelations();
		for(Entry<String, List<Expression>> entry : rel.entrySet())
		{
			String player = entry.getKey();
			boolean[] hasBeenTaken = new boolean[graph.getNumNodes()];
			Map<Integer, BitSet> player_class = new HashMap<Integer, BitSet>();
			List<BitSet> list = new ArrayList<BitSet>();
			for(Expression exp : entry.getValue())
			{
				StateSet allStates = UtilGraph.computeAllStatesExplicit(modelChecker.getLowLevel());
		        StateMapExplicit innerResult = (StateMapExplicit) modelChecker.check(exp, allStates);
		        UtilGraph.registerResult(graph, exp, innerResult);
		        allStates.close();
		        
		        EvaluatorExplicitBoolean evaluator = UtilEvaluatorExplicit.newEvaluatorBoolean(exp, graph, UtilPETL.collectIdentifiers(exp).toArray(new Expression[0]));
		        Value evalValues;
		        BitSet oneStates = UtilBitSet.newBitSetBounded(graph.getNumNodes());
		        for (int node = 0; node < graph.getNumNodes(); node ++) {
		        	if(hasBeenTaken[node])
		        		continue;
		        	NodeProperty isState = graph.getNodeProperty(CommonProperties.STATE);
		        	if(!isState.getBoolean(node))
		        	{
		        		hasBeenTaken[node] = true;
		        		continue;
		        	}
		        	
		            evalValues = graph.getNodeProperty(exp).get(node);
		            evaluator.setValues(evalValues);
		            boolean sat = evaluator.evaluateBoolean();
		            if (sat)
		            {
		            	hasBeenTaken[node] = true;
		            	oneStates.set(node);
		            }
		        }
		        
		        if(oneStates.isEmpty())
		        	continue;
		        
		        for(int state = oneStates.nextSetBit(0);state>=0;state=oneStates.nextSetBit(state+1))
		        {
		        	player_class.put(state, oneStates);
		        }
		        list.add(oneStates);
			}
			for(int i=0;i<hasBeenTaken.length;i++)
			{
				if(!hasBeenTaken[i])
				{
					BitSet singleton = UtilBitSet.newBitSetBounded(i+1);
					singleton.set(i);
					player_class.put(i, singleton);
					list.add(singleton);
				}
			}
			equivalenceClasses.put(player, list);
			equivalenceClassesMap.put(player, player_class);
		}
	}
	
	public boolean isInitalized()
	{
		return equivalenceClassesMap != null;
	}
	
	public List<BitSet> getClassesOfPlayer(String player)
	{
		List<BitSet> res = equivalenceClasses.get(player);
		if(res != null)
			return res;
		
		return new ArrayList<BitSet>();
	}
	
	public BitSet getClassFor(String player, int state)
	{
		BitSet res = equivalenceClassesMap.get(player).get(state).clone();
		
		assert res != null;
//		if(res != null)
//			return res;
//		res = UtilBitSet.newBitSetBounded(state+1);
//		res.set(state);
		return res;
	}
}
