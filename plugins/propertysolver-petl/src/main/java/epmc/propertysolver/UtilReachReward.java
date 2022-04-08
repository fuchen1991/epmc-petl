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
import epmc.graph.explicit.NodeProperty;
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

public class UtilReachReward {

	private static int timeLimit = 1;
	private static int bValueCoefficient = 1;
	private static int printTimeInterval = 1;
	private static ModelChecker modelChecker;
	private static GraphExplicit graph;
	private static List<String> players;
	private static EdgeProperty actionLabel;
	private static EdgeProperty probability;
	private static String emptyAction = "";
	private static EquivalenceClasses equivalenceClasses;
	private static Random random;
	private static int seed = 1000;
	private static int constructedNode = 0;
	private static NodeProperty stateReward;
	private static EdgeProperty transReward;
	private static BitSet reachSet;
	private static BitSet canNotReachSet;
	private static Map<Integer, Map<Integer, Double>> succStateRw;
	private static Map<Integer, Double> succConstRw;
	private static Set<Integer> fullExplored;
	private static List<FixedAction> fixedActions;
	
	private static void init(GraphExplicit gh, ModelChecker mc, NodeProperty sr, EdgeProperty tr)
	{
		modelChecker = mc;
		graph = gh;
		stateReward = sr;
		transReward = tr;
		actionLabel = graph.getEdgeProperty(CommonProperties.TRANSITION_LABEL);
		probability = graph.getEdgeProperty(CommonProperties.WEIGHT);
		players = ((ModelMAS) modelChecker.getModel()).getPlayers();
        equivalenceClasses = new EquivalenceClasses(modelChecker);
        Options options = Options.get();
        timeLimit = options.getInteger(OptionsUCT.UCT_TIME_LIMIT);
        bValueCoefficient = options.getInteger(OptionsUCT.BVALUE);
        printTimeInterval = options.getInteger(OptionsUCT.PRINT_TIME_INTERVAL);
        seed = options.getInteger(OptionsUCT.RANDOM_SEED);
        random = new Random(seed);
	}
	
	public static double[] computeProbabilities(BitSet unKnown, BitSet rs, BitSet cnrs, boolean min, StateSetExplicit computeForStates, GraphExplicit gh, ModelChecker mc, NodeProperty sr, EdgeProperty tr)
	{
		init(gh,mc,sr,tr);
		reachSet = rs;
		canNotReachSet = cnrs;
		
		int size = computeForStates.size();
		double[] resultValue = new double[size];
		for(int i=0;i<size;i++)
		{
			PropertySolverPOSGReachReward.countMemoryUsage();
			int state = computeForStates.getExplicitIthState(i);
			if(reachSet.get(state))
			{
				resultValue[i] = 0.0;
			}
			else if(canNotReachSet.get(state))
			{
				resultValue[i] = Double.POSITIVE_INFINITY;
			}
			else
			{
				double result = exploreWhenUCT(state, min);
				resultValue[i] = result;
			}
		}
		return resultValue;
	}
	
	private static double exploreWhenUCT(int state, boolean min)
	{
		System.out.println("Time limit: " + timeLimit);
		System.out.println("B value Coefficient: " + bValueCoefficient);
		System.out.println("Random seed: " + seed);
		UCTNode root = constructNode(state, emptyAction, true, min);
		exploreSearchTreeOnTheFly(root, min);
		System.out.println("Start to rollout...");
		int rolloutTimes = 0;
		long elapsed = 0;
		StopWatch watch = new StopWatch(true);
		List<FixedAction> bestActions = new ArrayList<FixedAction>();
		double bestResult = 0;

		while(watch.getTimeSeconds() < timeLimit)
		{
			if(watch.getTime() - elapsed * 1000  >= printTimeInterval * 1000)
			{
				PropertySolverPOSGReachReward.countMemoryUsage();
				elapsed += printTimeInterval;
				System.out.println("Elapsed time: " +  elapsed + "s Current result: " + root.getR()+ " rollouts: " + rolloutTimes + " nodes: " + constructedNode);
			}

			rolloutTimes += 1;
			Set<Integer> vs = new HashSet<Integer>();
			vs.add(state);
			succStateRw = new HashMap<Integer, Map<Integer, Double>>();
			succConstRw = new HashMap<Integer, Double>();
			fullExplored = new HashSet<Integer>();
			fixedActions = new ArrayList<FixedAction>();
			rollout_onthefly(root, min, vs);
			if(!min && root.getR()==Double.POSITIVE_INFINITY)
			{
				System.out.println("INFINITY found. Stop rollouts.");
				root.setR(Double.POSITIVE_INFINITY);
				break;
			}

			if(root.getVisitedTimes() <= 1 || (!min && root.getR() > bestResult) || (min && root.getR() < bestResult))
			{
				bestActions.clear();
				bestActions.addAll(fixedActions);
				bestResult = root.getR();
			}
		}
		
		System.out.println("Best actions:");
		for(FixedAction f : bestActions)
		{
			System.out.println(f.toString());
		}
		
		double final_res = root.getR();
		System.out.println("============================");
		System.out.println("Final result: " + final_res);
		System.out.println("Number of rollouts: " + rolloutTimes);
		System.out.println("Number of nodes: " + constructedNode);
		return final_res;
	}
	
	private static void rollout_onthefly(UCTNode node, boolean min, Set<Integer> visited)
	{
		if(node.isDecision())
		{
			List<UCTNode> successors = remainingSuccessors(node, fixedActions);
			UCTNode next = choseUnvisitedSucc(successors);
			if(next == null)
			{
				next = chooseSuccByUCT(node, successors);
			}
			
			addFixedActionInLocation( node, next);
			double srw = ValueDouble.as(stateReward.get(node.getState())).getDouble();
			//every index of successor has the same transition reward
			double trw = ValueDouble.as(transReward.get(next.getState(), 0)).getDouble();
			double currentReward = srw + trw;
			
			succConstRw.put(node.getState(), currentReward);
			rollout_onthefly(next,min, visited);
			addAllSuccValues(node.getState(), next.getState(), 1);
			
			replace(node.getState());
			reform(node.getState());
		}
		else
		{
			for(UCTNode succ : node.getSuccessors())
			{
				if(canNotReachSet.get(succ.getState()))
				{
					succConstRw.put(node.getState(), Double.POSITIVE_INFINITY);
					break;
				}
				else if(reachSet.get(succ.getState()))
				{
					continue;
				}
				else
				{
					if(!succ.isInitialized())
						exploreSearchTreeOnTheFly(succ, min);
					addOneSuccValue(node.getState(),succ.getState(), succ.getProbability());
					
					if(!visited.contains(succ.getState()))
					{
						visited.add(succ.getState());
						rollout_onthefly(succ,min, visited);
					}
				}
			}
		}
		double rw = succConstRw.containsKey(node.getState())? succConstRw.get(node.getState()) : 0;
		if(node.getVisitedTimes() == 0 || (!min && rw > node.getR()) || (min && rw < node.getR()))
		{
			node.setR(rw);
		}
		fullExplored.add(node.getState());
		node.increaseVisitedTimes();
	}
	
	private static void addFixedActionInLocation(UCTNode node, UCTNode next)
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
	
	private static List<UCTNode> remainingSuccessors(UCTNode node, List<FixedAction> fixedActions)
	{
		if(node.getSuccessors().size() == 1)
			return node.getSuccessors();
		
		Set<UCTNode> remove = new HashSet<UCTNode>();
		for(UCTNode succ : node.getSuccessors())
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
		List<UCTNode> remaining = new ArrayList<UCTNode>();
		for(UCTNode n : node.getSuccessors())
		{
			if(!remove.contains(n))
			{
				remaining.add(n);
			}
		}
		
		return remaining;
	}

	private static Map<Integer, Double> getOrCreate(int state)
	{
		Map<Integer, Double> innerMap;
		if(!succStateRw.containsKey(state))
			innerMap = new HashMap<Integer, Double>();
		else
		{
			innerMap = succStateRw.get(state);
			succStateRw.put(state, innerMap);
		}
		
		return innerMap;
	}
	
	private static void addAllSuccValues(int curr, int next, double pro)
	{
		Map<Integer, Double> currValues = getOrCreate(curr);
		Map<Integer, Double> nextValues = getOrCreate(next);
		for(int i : nextValues.keySet())
		{
			if(currValues.containsKey(i))
			{
				double sumPro = currValues.get(i) + nextValues.get(i)*pro;
				currValues.put(i, sumPro);
			}
			else
			{
				currValues.put(i, nextValues.get(i)*pro);
			}
		}
		succStateRw.put(curr, currValues);
		
		if(succConstRw.containsKey(next) )
		{
			double crw = succConstRw.containsKey(curr)? succConstRw.get(curr) : 0;
			succConstRw.put(curr, crw + succConstRw.get(next) * pro);
		}
	}
	
	private static void addOneSuccValue(int curr, int next, double pro)
	{
		Map<Integer, Double> currValues = getOrCreate(curr);
		
		if(currValues.containsKey(next))
		{
			double sumPro = currValues.get(next) + pro;
			currValues.put(next, sumPro);
		}
		else
		{
			currValues.put(next, pro);
		}
		succStateRw.put(curr, currValues);
	}
	
	private static void reform(int state)
	{
		Map<Integer, Double> currValues = succStateRw.get(state);
		if(!currValues.containsKey(state))
			return;
		
		double pro = currValues.get(state);
		currValues.remove(state);
		
		
		if(Math.abs(1-pro)<0.00000000001)
		{
			succConstRw.put(state, Double.POSITIVE_INFINITY);
			return;
		}
		else
		{
			Map<Integer, Double> newMap = new HashMap<Integer, Double>();
			for (int i : currValues.keySet())
			{
				double p = currValues.get(i);
				newMap.put(i, p/(1-pro));
			}
			
			succStateRw.put(state, newMap);
			
			if(succConstRw.containsKey(state) )
			{
				double crw = succConstRw.get(state);
				succConstRw.put(state, crw/(1-pro));
			}
		}
	}
	
	private static void replace(int state)
	{
		Map<Integer, Double> values = succStateRw.get(state);
		Stack<Integer> stack = new Stack<Integer>();
		
		for(int st : values.keySet())
		{
			if(fullExplored.contains(st))
			{
				stack.push(st);
			}
		}
		
		while(!stack.isEmpty())
		{
			int st = stack.pop();
			double pro = values.get(st);
			
			values.remove(st);
			Map<Integer, Double> val = succStateRw.get(st);
			
			for (int i : val.keySet())
			{
				double p = val.get(i);
				if(values.containsKey(i))
				{
					double sumPro = values.get(i) + p*pro;
					values.put(i, sumPro);
				}
				else
				{
					values.put(i, p*pro);
				}
				if(fullExplored.contains(i) && !stack.contains(i))
				{
					stack.push(i);
				}
			}
			if(succConstRw.containsKey(st) || succConstRw.containsKey(state))
			{
				double srw = succConstRw.containsKey(st)? succConstRw.get(st) : 0;
				double crw = succConstRw.containsKey(state)? succConstRw.get(state) : 0;
				succConstRw.put(state, crw+ srw*pro);
			}
		}
		succStateRw.put(state, values);
	}
	
	private static UCTNode choseUnvisitedSucc(List<UCTNode> successors)
	{
		List<Integer> indexes = new ArrayList<Integer>();
		for(UCTNode succ : successors)
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

	private static UCTNode chooseSuccByUCT(UCTNode node, List<UCTNode> successors)
	{
		double UCTValue = 0;
		List<Integer> indexes = new ArrayList<Integer>();
		double B = estimateB(node);
		for(int i=0;i<successors.size();i++)
		{
			UCTNode succ = successors.get(i);
			double currValue = B * Math.sqrt(Math.log(node.getVisitedTimes()) / succ.getVisitedTimes()) + succ.getR();
			
			if(currValue > UCTValue || UCTValue == 0)
			{
				UCTValue = currValue;
				indexes.clear();
				indexes.add(i);
			}
			if(currValue == UCTValue)
			{
				indexes.add(i);
			}
		}
		int index = random.nextInt(indexes.size());
		return successors.get(indexes.get(index));
	}


	private static double estimateB(UCTNode node)
	{
		double res = 1;
		if(node.getR() > 0)
		{
			res = node.getR();
		}
		return res * bValueCoefficient;
	}
	
	private static UCTNode constructNode(int state, String action, boolean isDecision, boolean min)
	{
		constructedNode += 1;
		UCTNode node = new UCTNode(state, action, isDecision);
		node.setVisitedTimes(0);
		if(min)
			node.setR(Double.POSITIVE_INFINITY);
		else
			node.setR(0);
		return node;
	}
	
	private static void exploreSearchTreeOnTheFly(UCTNode node,  boolean min)
	{
		int state = node.getState();
		for (int iter = 0; iter < graph.getNumSuccessors(state); iter++)
		{
			int succ = graph.getSuccessorNode(state, iter);
			Action ac = actionLabel.getObject(state, iter);
            String nextAction = ac.getName();
            UCTNode succNode = constructNode(succ, nextAction, false, min);
            for (int index = 0; index < graph.getNumSuccessors(succ); index++)
    		{
    			int dst = graph.getSuccessorNode(succ, index);
    			double pro = ((ValueDouble) probability.get(succ, index)).getDouble();
    			UCTNode dstNode = constructNode(dst, emptyAction, true, min);
    			dstNode.setProbability(pro);
    			succNode.addSuccessor(dstNode);
    		}
            
            node.addSuccessor(succNode);
		}
		node.setInitialized(true);
	}
	
}
