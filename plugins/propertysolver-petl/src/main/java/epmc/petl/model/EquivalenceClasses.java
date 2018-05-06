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
import epmc.util.BitSet;
import epmc.util.UtilBitSet;
import epmc.value.Value;
import epmc.prism.model.ModelMAS;

/**
 * Equivalence classes of the agents
 * 
 * @author Chen Fu
 */

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
			boolean[] helper = new boolean[graph.getNumNodes()];
			Map<Integer, BitSet> player_class = new HashMap<Integer, BitSet>();
			List<BitSet> list = new ArrayList<BitSet>();
			for(Expression exp : entry.getValue())
			{
				StateSet allStates = UtilGraph.computeAllStatesExplicit(modelChecker.getLowLevel());
		        StateMapExplicit innerResult = (StateMapExplicit) modelChecker.check(exp, allStates);
		        UtilGraph.registerResult(graph, exp, innerResult);
		        allStates.close();
		        
		        EvaluatorExplicitBoolean evaluator = UtilEvaluatorExplicit.newEvaluatorBoolean(exp, graph, exp);
		        Value evalValues;
		        BitSet oneStates = UtilBitSet.newBitSetBounded(graph.getNumNodes());
		        for (int node = 0; node < graph.getNumNodes(); node ++) {
		        	if(helper[node])
		        		continue;
		        	NodeProperty isState = graph.getNodeProperty(CommonProperties.STATE);
		        	if(!isState.getBoolean(node))
		        	{
		        		helper[node] = true;
		        		continue;
		        	}
		        	
		            evalValues = graph.getNodeProperty(exp).get(node);
		            evaluator.setValues(evalValues);
		            boolean sat = evaluator.evaluateBoolean();
		            if (sat)
		            {
		            	helper[node] = true;
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
			for(int i=0;i<helper.length;i++)
			{
				if(!helper[i])
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

		return res;
	}
}
