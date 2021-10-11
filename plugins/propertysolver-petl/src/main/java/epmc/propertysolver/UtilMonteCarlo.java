package epmc.propertysolver;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Random;
import java.util.Set;
import java.util.Stack;

import epmc.graph.CommonProperties;
import epmc.graph.explicit.EdgeProperty;
import epmc.graph.explicit.GraphExplicit;
import epmc.graph.explicit.StateSetExplicit;
import epmc.jani.model.Action;
import epmc.modelchecker.ModelChecker;
import epmc.options.Options;
import epmc.petl.model.EquivalenceClasses;
import epmc.petl.model.ModelMAS;
import epmc.prism.model.Module;
import epmc.util.BitSet;
import epmc.util.StopWatch;
import epmc.value.ValueDouble;

public class UtilMonteCarlo {
	private static int timeLimit = 10;
	private static int printTimeInterval = 1;
	private static ModelChecker modelChecker;
	private static GraphExplicit graph;
	private static List<String> players;
	private static EdgeProperty actionLabel;
	private static EdgeProperty probability;
	private static BitSet oneStates;
	private static BitSet zeroStates;
	private static EquivalenceClasses equivalenceClasses;
	private static Random random;
	private static int seed = 1000;
	private static int[] visitedTimes;
	
	private static void init(GraphExplicit gh, ModelChecker mc)
	{
		modelChecker = mc;
		graph = gh;
		actionLabel = graph.getEdgeProperty(CommonProperties.TRANSITION_LABEL);
		probability = graph.getEdgeProperty(CommonProperties.WEIGHT);
		List<Module> modules = ((ModelMAS) modelChecker.getModel()).getModelPrism().getModules();
        players = new ArrayList<String>();
        equivalenceClasses = new EquivalenceClasses(modelChecker);
        for(Module m : modules)
        {
        	players.add(m.getName());
        }
        Options options = Options.get();
        timeLimit = options.getInteger(OptionsUCT.UCT_TIME_LIMIT);
        printTimeInterval = options.getInteger(OptionsUCT.PRINT_TIME_INTERVAL);
        seed = options.getInteger(OptionsUCT.RANDOM_SEED);
        random = new Random(seed);
        
        System.out.println(graph.getNumNodes() + " nodes");
        visitedTimes = new int[graph.getNumNodes()];
	}
	
	public static double[] computeProbabilities(BitSet oneSet, BitSet zeroSet, boolean min, boolean negate, BitSet unKnown, StateSetExplicit computeForStates, GraphExplicit gh, ModelChecker mc)
	{
		init(gh,mc);
		oneStates = oneSet;
		zeroStates = zeroSet;
		
		int size = computeForStates.size();
		double[] resultValue = new double[size];
		
		for(int i=0;i<size;i++)
		{
			int state = computeForStates.getExplicitIthState(i);
			if(oneSet.get(state))
			{
				if(negate)
					resultValue[i] = 0.0;
				else
					resultValue[i] = 1.0;
			}
			else if(zeroSet.get(state))
			{
				if(negate)
					resultValue[i] = 1.0;
				else
					resultValue[i] = 0.0;
			}
			else
			{
				double result = explore(state, oneSet, zeroSet, min);
				if(negate)
					resultValue[i] = 1.0 - result;
				else
					resultValue[i] = result;
			}
		}
		return resultValue;
	}
	
	private static double explore(int state, BitSet oneSet, BitSet zeroSet, boolean min)
	{
		int rolloutTimes = 0;
		long elapsed = 0;
		StopWatch watch = new StopWatch(true);
		Set<Integer> visitedStates = new HashSet<Integer>();
		visitedStates.add(state);
		double result = 0.0;
		if(min)
		{
			while(watch.getTimeSeconds() < timeLimit)
			{
				
			}
		}
		else
		{
			while(watch.getTimeSeconds() < timeLimit)
			{
				if(watch.getTime() - elapsed * 1000  >= printTimeInterval * 1000)
				{
					elapsed += printTimeInterval;
					System.out.println("Elapsed time: " +  elapsed + "s Current result: " + result + " rollouts: " + rolloutTimes);
				}
				rolloutTimes += 1;
				MonteCarloNode root = constructNode(state, true);
				visitedTimes[state]++;
//				root.increaseVisitedTimes();
				Map<Integer, MonteCarloNode> visited = new HashMap<Integer, MonteCarloNode>();
				visited.put(state, root);
				rollout_max(root, new ArrayList<FixedAction>(),visited);
				double res = 0;
				if(root.getSuccessor_values().containsKey("1"))
					res = root.getSuccessor_values().get("1");
				
				if(res > result)
					result = res;
			}
		}
		
		return result;
	}
	
	private static void rollout_max(MonteCarloNode node, List<FixedAction> fixedActions, Map<Integer, MonteCarloNode> visited)
	{
		if(node.isDecision())
		{
			List<MonteCarloNode> successors = remainingSuccessors(node, fixedActions);
			MonteCarloNode next = choseUnvisitedSucc(successors);
			if(next == null)
			{
				next = chooseSuccByUCT(node, successors);
			}
			visitedTimes[next.getState()]++;
			addFixedActionInLocation(fixedActions, node, next);
			rollout_max(next, fixedActions,visited);
			node.addupSucc(next.getSuccessor_values(), 1);
			node.reformulateSuccValues();
		}
		else
		{
			for(MonteCarloNode succ : node.getSuccessors())
			{
				visitedTimes[succ.getState()]++;
				if(oneStates.get(succ.getState()))
				{
					node.addSuccValue("1", succ.getProbability());
				}
				else if(zeroStates.get(succ.getState()))
				{
					node.addSuccValue("0", succ.getProbability());
				}
				else if(visited.containsKey(succ.getState()))
				{
					if(!succ.isFullExplored())
					{
						node.addSuccValue("x" + succ.getState(), succ.getProbability());
					}
					else
					{
						Stack<Entry<String, Double>> values = new Stack<Entry<String, Double>>();
						for(Entry<String, Double> entry : succ.getSuccessor_values().entrySet())
						{
							values.add(entry);
						}
						while(!values.empty())
						{
							Entry<String, Double> entry = values.pop();
							String string = entry.getKey();
							if(!string.startsWith("x"))
							{
								node.addSuccValue(string, entry.getValue());
							}
							else
							{
								int st = Integer.parseInt(entry.getKey().substring(1));
								MonteCarloNode inter = visited.get(st);
								if(!inter.isFullExplored())
								{
									node.addSuccValue(string, entry.getValue());
								}
								else
								{
									HashMap<String, Double> hm = new HashMap<String, Double>();
									hm.putAll(inter.getSuccessor_values());
									for(String key : hm.keySet())
									{
										hm.put(key, hm.get(key)*entry.getValue());
									}
									for(Entry<String, Double> en : hm.entrySet())
									{
										values.add(en);
									}
								}
							}
						}
					}
				}
				else
				{
					visited.put(succ.getState(), succ);
					rollout_max(succ, fixedActions,visited);
					node.addupSucc(succ.getSuccessor_values(), succ.getProbability());
				}
			}
			node.setFullExplored(true);
		}

	}
	
	private static MonteCarloNode constructNode(int state, boolean isDecision) 
	{
		MonteCarloNode node = new MonteCarloNode(state,isDecision);
		
		return node;
	}
	
	private static List<MonteCarloNode> remainingSuccessors(MonteCarloNode node, List<FixedAction> fixedActions)
	{
		exploreSuccessors(node);
		
//		if(node.getSuccessors().size() == 1)
//			return node.getSuccessors();
		
		Set<MonteCarloNode> remove = new HashSet<MonteCarloNode>();
		for(MonteCarloNode succ : node.getSuccessors())
		{
			String action = succ.getAction();
			int state = node.getState();
			for(FixedAction fix : fixedActions)
			{
				if(equivalenceClasses.isEquivalent(fix.player, fix.state, state))
				{
					String localAction = fix.action.split(",")[players.indexOf(fix.player)];
					String currLocalAction = action.split(",")[players.indexOf(fix.player)];
					if(!localAction.equals(currLocalAction))
					{
						remove.add(succ);
						break;
					}
				}
			}
		}
		List<MonteCarloNode> remaining = new ArrayList<MonteCarloNode>();
		for(MonteCarloNode n : node.getSuccessors())
		{
			if(!remove.contains(n))
			{
				remaining.add(n);
			}
		}
		return remaining;
	}
	
	//optimize this to reuse some parts of the nodes
	private static void exploreSuccessors(MonteCarloNode node)
	{
		int state = node.getState();
		for (int iter = 0; iter < graph.getNumSuccessors(state); iter++)
		{
			int succ = graph.getSuccessorNode(state, iter);
			Action ac = actionLabel.getObject(state, iter);
            String nextAction = ac.getName();
            MonteCarloNode succNode = constructNode(succ, false);
            succNode.setAction(nextAction);
            for (int index = 0; index < graph.getNumSuccessors(succ); index++)
    		{
    			int dst = graph.getSuccessorNode(succ, index);
    			double pro = ((ValueDouble) probability.get(succ, index)).getDouble();
    			MonteCarloNode dstNode = constructNode(dst, true);
    			dstNode.setProbability(pro);
    			succNode.addSuccessor(dstNode);
    		}
            
            node.addSuccessor(succNode);
		}
	}
	
	private static MonteCarloNode choseUnvisitedSucc(List<MonteCarloNode> successors)
	{
		List<Integer> indexes = new ArrayList<Integer>();
		for(MonteCarloNode succ : successors)
		{
//			if(succ.getVisitedTimes() == 0)
			if(visitedTimes[succ.getState()] == 0)
			{
				indexes.add(successors.indexOf(succ));
			}
		}
		if(indexes.size() == 0)
			return null;
		int index = random.nextInt(indexes.size());
		return successors.get(indexes.get(index));
	}
	
	private static MonteCarloNode chooseSucc(MonteCarloNode node, List<MonteCarloNode> successors)
	{
		int index = 0;
		int vt = -1;
		for(int i=0;i<successors.size();i++)
		{
			MonteCarloNode succ = successors.get(i);
//			if(vt == -1 || succ.getVisitedTimes() > vt)
			if(vt == -1 || visitedTimes[succ.getState()] < vt)
			{
//				vt = succ.getVisitedTimes();
				vt = visitedTimes[succ.getState()];
				index = i;
			}
		}
		return successors.get(index);
	}
	
	private static MonteCarloNode chooseSuccByUCT(MonteCarloNode node, List<MonteCarloNode> successors)
	{
		double UCTValue = 0;
		double B = estimateB(node)*10;
		int index = 0; 
		for(int i=0;i<successors.size();i++)
		{
			MonteCarloNode succ = successors.get(i);
			double currValue = B * Math.sqrt(Math.log(visitedTimes[node.getState()]) / visitedTimes[succ.getState()]) + estimateB(succ);
			if(currValue > UCTValue || UCTValue == 0)
			{
				UCTValue = currValue;
				index = i;
			}
		}
		return successors.get(index);
	}
	
	private static double estimateB(MonteCarloNode node)
	{
		double oneV = 0;
		double zeroV = 0;
		if(node.getSuccessor_values().containsKey("1"))
			oneV = node.getSuccessor_values().get("1");
		if(node.getSuccessor_values().containsKey("0"))
			zeroV = node.getSuccessor_values().get("0");
		
		return oneV + (1-zeroV)/2;
	}
	
	private static void addFixedActionInLocation(List<FixedAction> fixedActions, MonteCarloNode node, MonteCarloNode next)
	{
		String globalAction = next.getAction();
		int state = node.getState();
		for(int i=0;i<players.size();i++)
		{
			FixedAction fa = new FixedAction(players.get(i), state, globalAction);
			if(!fixedActions.contains(fa))
			{
				fixedActions.add(fa);
			}
		}
	}
}
