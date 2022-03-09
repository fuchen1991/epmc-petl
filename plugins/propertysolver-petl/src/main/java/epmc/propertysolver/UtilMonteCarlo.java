package epmc.propertysolver;

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
	private static int bValueCoefficient = 1;
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
//	private static Map<Integer, MonteCarloNode> monterCarloNodes;
	private static List<FixedAction> fixedActions;
	private static Map<Integer, RolloutNode> rolloutNodes;
	
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
        bValueCoefficient = options.getInteger(OptionsUCT.BVALUE);
        printTimeInterval = options.getInteger(OptionsUCT.PRINT_TIME_INTERVAL);
        seed = options.getInteger(OptionsUCT.RANDOM_SEED);
        random = new Random(seed);
        
//        monterCarloNodes = new HashMap<Integer, MonteCarloNode>();
        
        
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
			
			PropertySolverPETLUntilUCTWithoutDepth.countMemoryUsage();
		}
		return resultValue;
	}
	
	private static double explore(int state, BitSet oneSet, BitSet zeroSet, boolean min)
	{
		System.out.println("Time limit: " + timeLimit);
		System.out.println("B value Coefficient: " + bValueCoefficient);
		System.out.println("Random seed: " + seed);
//		List<FixedAction> bestActions = new ArrayList<FixedAction>();
//		double bestResult = 0;

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
				PropertySolverPETLUntilUCTWithoutDepth.countMemoryUsage();
				elapsed += printTimeInterval;
				System.out.println("Elapsed time: " +  elapsed + "s Current result: " + result + " rollouts: " + rolloutTimes);
			}
			rolloutTimes += 1;
			rolloutNodes = new HashMap<Integer, RolloutNode>();
			
			MonteCarloNode root = constructNode(state, true);
			root.increaseVisitedTimes();
			Set<Integer> visited = new HashSet<Integer>();
			visited.add(state);
			fixedActions = new ArrayList<FixedAction>();
			rollout(min, root, visited);
			
			double res = rolloutNodes.get(state).getValue("1");
//			if(res == -1)
//				res = 0;
//			System.out.println(res);
//			System.exit(0);
			if((min && result > res) || (!min && result < res))
			{
				result = res;
			}
			if((min && result == 0) || (!min && result == 1))
				break;
			
//			if(root.getVisitedTimes() <= 1 || result < bestResult)
//			{
//				bestActions.clear();
//				bestActions.addAll(fixedActions);
//				bestResult = result;
//			}
		}

//		System.out.println("Best actions:");
//		for(FixedAction f : bestActions)
//		{
//			System.out.println(f.toString());
//		}
		System.out.println("Final result: " + result);
		return result;
	}
	
	private static void rollout(boolean min, MonteCarloNode node,  Set<Integer> visited)
	{
//		System.out.println("enter " + node.getState() + "  " + node.isDecision());
//		if(!node.isDecision())
//		{
//			System.out.println(node.getSuccessors().size() + "  succ");
//			for(MonteCarloNode succ : node.getSuccessors())
//			{
//				System.out.print(succ.getState() + "  ");
//			}
//			System.out.println();
//		}

		RolloutNode nodeRoll = constructRolloutNode(node.getState());
		if(node.isDecision())
		{
			List<MonteCarloNode> successors = remainingSuccessors(node);
			MonteCarloNode next = choseUnvisitedSucc(successors);
			if(next == null)
			{
				next = chooseSuccUCT(node, successors);
			}
			next.increaseVisitedTimes();
		
			addFixedActionInLocation(node, next);
			rollout(min, next, visited);
			
			RolloutNode nextRoll = constructRolloutNode(next.getState());
			nodeRoll.addupSucc(nextRoll.getSuccessor_values(), 1);
			
			replace(nodeRoll);
			nodeRoll.reformulateSuccValues();
		}
		else
		{
			for(MonteCarloNode succ : node.getSuccessors())
			{
				succ.increaseVisitedTimes();
				if(oneStates.get(succ.getState()))
				{
//					System.out.println(succ.getState() + " is 1 state " + succ.getProbability(node.getState()));
					nodeRoll.addSuccValue("1", succ.getProbability(node.getState()));
				}
				else if(zeroStates.get(succ.getState()))
				{
//					System.out.println(succ.getState() + " is 0 state " + succ.getProbability(node.getState()));
					nodeRoll.addSuccValue("0", succ.getProbability(node.getState()));
				}
				else
				{
					nodeRoll.addSuccValue("x" + succ.getState(), succ.getProbability(node.getState()));
					if(!visited.contains(succ.getState()))
					{
						visited.add(succ.getState());
						rollout(min, succ, visited);
					}
//					else
//					{
//						System.out.println(succ.getState() + " has been visited");
//					}
				}
			}
		}
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
//		System.out.println(node.getState() + " full explored");
//		printNode(node.getState());
	}
	
	private static void replace(RolloutNode node)
	{
//		printNode(node);
		Stack<RolloutNode> stack = new Stack<RolloutNode>();
		for (String k : node.getSuccessor_values().keySet())
		{
			if(k.startsWith("x"))
			{
				int st = Integer.parseInt(k.substring(1));
				RolloutNode interRoll = constructRolloutNode(st);
				if(interRoll.isFullExplored())
				{
//					System.out.println(interRoll.getState() + " FULL");
					stack.add(interRoll);
				}
			}
		}
		while(!stack.isEmpty())
		{
			RolloutNode rn = stack.pop();
			int state = rn.getState();
			double pro = node.getValue("x" + state);
			assert pro != -1;
			
			node.removeValue("x" + state);
			
			for(String kk : rn.getSuccessor_values().keySet())
			{
				double pp = rn.getValue(kk);
				node.addSuccValue(kk, pro *pp);
				if(kk.startsWith("x"))
				{
					int st = Integer.parseInt(kk.substring(1));
					RolloutNode interRoll = constructRolloutNode(st);
					if(interRoll.isFullExplored())
						stack.add(interRoll);
				}
//				printNode(node);
			}
//			if(node.getState() == 9)
//			System.exit(0);
		}
	}
	
	private static MonteCarloNode constructNode(int state, boolean isDecision) 
	{
//		if(monterCarloNodes.containsKey(state))
//			return monterCarloNodes.get(state);
		
		MonteCarloNode node = new MonteCarloNode(state,isDecision);
//		monterCarloNodes.put(state, node);
		return node;
	}
	
	private static RolloutNode constructRolloutNode(int state) {
		if(rolloutNodes.containsKey(state))
			return rolloutNodes.get(state);
		
		RolloutNode roll = new RolloutNode(state);
		rolloutNodes.put(state, roll);
		return roll;
	}
	
	private static List<MonteCarloNode> remainingSuccessors(MonteCarloNode node)
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
            
//            if(succ == 990)
//            	System.out.println(graph.getNumSuccessors(succ) + " *************");
            
            for (int index = 0; index < graph.getNumSuccessors(succ); index++)
    		{
    			int dst = graph.getSuccessorNode(succ, index);
    			double pro = ((ValueDouble) probability.get(succ, index)).getDouble();
    			MonteCarloNode dstNode = constructNode(dst, true);
//    			System.out.println("ttttt" + dst + "   " + monterCarloNodes.containsKey(state) + "   " + dstNode.contains(succ));
//    			if(dstNode.contains(succ))
//    			{
//    				System.out.println("ttttt");
//    				dstNode.setProbability(succ, dstNode.getProbability(succ)+pro);
//    			}
//    			else
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
		List<Integer> indexes = new ArrayList<Integer>();
		double B = estimateB(node);
		
//		int index = 0; 
		for(int i=0;i<successors.size();i++)
		{
			MonteCarloNode succ = successors.get(i);
			double currValue = B * Math.sqrt(Math.log(node.getVisitedTimes()) / succ.getVisitedTimes()) + succ.getCurrentReward();
			if(currValue > UCTValue || UCTValue == 0)
			{
				UCTValue = currValue;
				indexes.clear();
				indexes.add(i);
//				index = i;
			}
			if(currValue == UCTValue)
			{
				indexes.add(i);
			}
		}
		int index = random.nextInt(indexes.size());
		return successors.get(indexes.get(index));
//		return successors.get(index);
	}
	
	private static double estimateB(MonteCarloNode node)
	{
		double res = 1;
		if(node.getCurrentReward() > 0)
		{
			res = node.getCurrentReward();
		}
		
		return res * bValueCoefficient;
	}
	
	private static void addFixedActionInLocation( MonteCarloNode node, MonteCarloNode next)
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
	
	private static void printNode(int state)
	{
		RolloutNode node = constructRolloutNode(state);
		System.out.println(state + "==============");
		for(String s : node.getSuccessor_values().keySet())
		{
			System.out.println(s + " : " + node.getValue(s));
		}
	}
	
	private static void printNode(RolloutNode node)
	{
		System.out.println(node.getState() + "==============");
		for(String s : node.getSuccessor_values().keySet())
		{
			System.out.println(s + " : " + node.getValue(s));
		}
	}
}
