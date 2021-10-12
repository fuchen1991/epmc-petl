package epmc.propertysolver;

import java.math.BigDecimal;
import java.math.RoundingMode;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
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
	private static Map<Integer, MonteCarloNode> monterCarloNodes;
	
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
        
        monterCarloNodes = new HashMap<Integer, MonteCarloNode>();
        
        System.out.println(graph.getNumNodes() + " nodes");
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
		double result = 0.0;
		if(min)
			result = 1.0;
		
		while(watch.getTimeSeconds() < timeLimit)
		{
			if(watch.getTime() - elapsed * 1000  >= printTimeInterval * 1000)
			{
				elapsed += printTimeInterval;
				System.out.println("Elapsed time: " +  elapsed + "s Current result: " + result + " rollouts: " + rolloutTimes);
			}
			rolloutTimes += 1;
			Map<Integer, RolloutNode> rolloutNodes = new HashMap<Integer, RolloutNode>();
			
			MonteCarloNode root = constructNode(state, true);
			root.increaseVisitedTimes();
			RolloutNode rollRoot = constructRolloutNode(state, rolloutNodes);
			rolloutNodes.put(state, rollRoot);
			Set<Integer> visited = new HashSet<Integer>();
			visited.add(state);
			
			rollout(min, root, new ArrayList<FixedAction>(),visited,rolloutNodes);
			
			double res;
			if(min)
			{
				double r = rollRoot.getValue("0");
				if(r == -1)
					r = 0;
				res = 1 - r;
				if(res < result)
					result = res;
			}
			else
			{
				res = rollRoot.getValue("1");
				if(res > result)
					result = res;
			}
			
			//Because of loss of precision
			BigDecimal num = new BigDecimal(result + "");
			result = num.setScale(15, RoundingMode.HALF_EVEN).doubleValue();
			
//			Runtime runtime = Runtime.getRuntime();
//			runtime.gc();
//	        long memory = runtime.totalMemory() - runtime.freeMemory();
//	        System.out.println("Used memory is megabytes: " + memory/(1024L*1024L));
			
//			System.out.println("Finish a rollout, the result of this rollout is " + res + " the current best result is " + result);
		}
				
		return result;
	}
	
	private static void rollout(boolean min, MonteCarloNode node, List<FixedAction> fixedActions, Set<Integer> visited, Map<Integer, RolloutNode> rolloutNodes)
	{
		RolloutNode nodeRoll = constructRolloutNode(node.getState(), rolloutNodes);
		if(node.isDecision())
		{
//			System.out.println(node.getState() + " is decision node");
			List<MonteCarloNode> successors = remainingSuccessors(node, fixedActions);
			MonteCarloNode next = choseUnvisitedSucc(successors);
			if(next == null)
			{
				next = chooseSuccUCT(node, successors);
			}
			next.increaseVisitedTimes();
//			System.out.println("choose next: " + next.getState() + "  " + next.getAction(node.getState()));
			
			addFixedActionInLocation(fixedActions, node, next);
			rollout(min, next, fixedActions,visited,rolloutNodes);
			
			RolloutNode nextRoll = constructRolloutNode(next.getState(), rolloutNodes);
			nodeRoll.addupSucc(nextRoll.getSuccessor_values(), 1);
			nodeRoll.reformulateSuccValues();
		}
		else
		{
//			System.out.println(node.getState() + " is Not decision node");
			for(MonteCarloNode succ : node.getSuccessors())
			{
//				System.out.println("Succ : " + succ.getState() + "  " + succ.getProbability(node.getState()) + " of state " + node.getState());
				succ.increaseVisitedTimes();
				RolloutNode succRoll = constructRolloutNode(succ.getState(), rolloutNodes);
				if(oneStates.get(succ.getState()))
				{
//					System.out.println(succ.getState() + "  is one state");
					nodeRoll.addSuccValue("1", succ.getProbability(node.getState()));
				}
				else if(zeroStates.get(succ.getState()))
				{
//					System.out.println(succ.getState() + "  is zero state");
					nodeRoll.addSuccValue("0", succ.getProbability(node.getState()));
				}
				else if(visited.contains(succ.getState()))
				{
//					System.out.println(succ.getState() + "  has been visited");
					if(!succRoll.isFullExplored())
					{
						nodeRoll.addSuccValue("x" + succ.getState(), succ.getProbability(node.getState()));
					}
					else
					{
						Stack<String> keys = new Stack<String>();
						Stack<Double> pros = new Stack<Double>();
						for(String k : succRoll.getSuccessor_values().keySet())
						{
							keys.push(k);
							pros.push(succRoll.getValue(k)*succ.getProbability(node.getState()));
						}
						while(!keys.empty())
						{
							String key = keys.pop();
							double value = pros.pop();
							
							if(!key.startsWith("x"))
							{
								nodeRoll.addSuccValue(key, value);
							}
							else
							{
								int st = Integer.parseInt(key.substring(1));
								RolloutNode interRoll = constructRolloutNode(st, rolloutNodes);
								if(!interRoll.isFullExplored())
								{
									nodeRoll.addSuccValue(key, value);
								}
								else
								{
									for(String k : interRoll.getSuccessor_values().keySet())
									{
										keys.push(k);
										pros.push(interRoll.getValue(k)*value);
									}
								}
							}
						}
					}
				}
				else
				{
					visited.add(succ.getState());
//					System.out.println(succ.getState() + "  needs to rollout");
					rollout(min, succ, fixedActions,visited,rolloutNodes);
					nodeRoll.addupSucc(succRoll.getSuccessor_values(), succ.getProbability(node.getState()));
				}
			}
			
//			System.out.println("Finish all successors of " + node.getState());
			//store the max reward across multi rollouts
			if(min)
			{
				if(nodeRoll.getValue("0") > node.getCurrentReward())
				{
					node.setCurrentReward(nodeRoll.getValue("0"));
				}
			}
			else
			{
				if(nodeRoll.getValue("1") > node.getCurrentReward())
				{
					node.setCurrentReward(nodeRoll.getValue("1"));
				}
			}

			nodeRoll.setFullExplored(true);
		}
	}
	
	private static MonteCarloNode constructNode(int state, boolean isDecision) 
	{
		if(monterCarloNodes.containsKey(state))
			return monterCarloNodes.get(state);
		
		MonteCarloNode node = new MonteCarloNode(state,isDecision);
		monterCarloNodes.put(state, node);
		return node;
	}
	
	private static RolloutNode constructRolloutNode(int state, Map<Integer, RolloutNode> rolloutNodes) {
		if(rolloutNodes.containsKey(state))
			return rolloutNodes.get(state);
		
		RolloutNode roll = new RolloutNode(state);
		rolloutNodes.put(state, roll);
		return roll;
	}
	
	private static List<MonteCarloNode> remainingSuccessors(MonteCarloNode node, List<FixedAction> fixedActions)
	{
		exploreSuccessors(node);
		
		Set<MonteCarloNode> remove = new HashSet<MonteCarloNode>();
		for(MonteCarloNode succ : node.getSuccessors())
		{
			String action = succ.getAction(node.getState());
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
	
	private static void exploreSuccessors(MonteCarloNode node)
	{
		int state = node.getState();
		//this node has been explored before
		if(node.isExplored())
			return;
		
		for (int iter = 0; iter < graph.getNumSuccessors(state); iter++)
		{
			int succ = graph.getSuccessorNode(state, iter);
			Action ac = actionLabel.getObject(state, iter);
            String nextAction = ac.getName();
            MonteCarloNode succNode = constructNode(succ, false);
            succNode.setAction(state, nextAction);
            
//            if(succ == 163)
//			{
//				System.out.println(graph.getNumSuccessors(succ));
//				for (int index = 0; index < graph.getNumSuccessors(succ); index++)
//				{
//					int dst = graph.getSuccessorNode(succ, index);
//					double pro = ((ValueDouble) probability.get(succ, index)).getDouble();
//					System.out.println("state " + dst + "  " + pro);
//				}
//				System.out.println("-------------------");
////				System.exit(0);
//			}
            
            for (int index = 0; index < graph.getNumSuccessors(succ); index++)
    		{
    			int dst = graph.getSuccessorNode(succ, index);
    			double pro = ((ValueDouble) probability.get(succ, index)).getDouble();
    			MonteCarloNode dstNode = constructNode(dst, true);
    			dstNode.setProbability(succ, pro);
    			succNode.addSuccessor(dstNode);
    		}
            
            node.addSuccessor(succNode);
		}
		node.setExplored(true);
	}
	
	private static MonteCarloNode choseUnvisitedSucc(List<MonteCarloNode> successors)
	{
		List<Integer> indexes = new ArrayList<Integer>();
		for(MonteCarloNode succ : successors)
		{
			if(succ.getVisitedTimes() == 0)
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
			if(vt == -1 || succ.getVisitedTimes() < vt)
			{
				vt = succ.getVisitedTimes();
				index = i;
			}
		}
		return successors.get(index);
	}
	
	private static MonteCarloNode chooseSuccRandom(MonteCarloNode node, List<MonteCarloNode> successors)
	{
		int index = random.nextInt(successors.size());
		return successors.get(index);
	}
	
	
	private static MonteCarloNode chooseSuccUCT(MonteCarloNode node, List<MonteCarloNode> successors)
	{
		double UCTValue = 0;
		double B = estimateB(node) * 9;
		if(B <= 0)
			B = 1;
		
		int index = 0; 
		for(int i=0;i<successors.size();i++)
		{
			MonteCarloNode succ = successors.get(i);
			double currValue = B * Math.sqrt(Math.log(node.getVisitedTimes()) / succ.getVisitedTimes()) + estimateB(succ);
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
//		System.out.println(node.getCurrentReward());
		return node.getCurrentReward();
	}
	
	private static void addFixedActionInLocation(List<FixedAction> fixedActions, MonteCarloNode node, MonteCarloNode next)
	{
		int state = node.getState();
		String globalAction = next.getAction(state);
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
