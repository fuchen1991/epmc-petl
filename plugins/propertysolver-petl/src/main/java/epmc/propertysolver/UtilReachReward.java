package epmc.propertysolver;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

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
	private static boolean InfinityFound = false;
	
	private static void init(GraphExplicit gh, ModelChecker mc, NodeProperty sr, EdgeProperty tr)
	{
		modelChecker = mc;
		graph = gh;
		stateReward = sr;
		transReward = tr;
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
		
		while(watch.getTimeSeconds() < timeLimit)
		{
			if(watch.getTime() - elapsed * 1000  >= printTimeInterval * 1000)
			{
				PropertySolverPOSGReachReward.countMemoryUsage();
				elapsed += printTimeInterval;
				System.out.println("Elapsed time: " +  elapsed + "s Current result: " + root.getR()+ " rollouts: " + rolloutTimes + " nodes: " + constructedNode);
			}
			root.increaseVisitedTimes();
			rolloutTimes += 1;
			rollout_onthefly(root, new ArrayList<FixedAction>(),min);
			if(!min && InfinityFound)
			{
				System.out.println("INFINITY found. Stop rollouts.");
				root.setR(Double.POSITIVE_INFINITY);
				break;
			}
			InfinityFound = false;
		}
		
		double final_res = root.getR();
		System.out.println("============================");
		System.out.println("Final result: " + final_res);
		System.out.println("Number of rollouts: " + rolloutTimes);
		System.out.println("Number of nodes: " + constructedNode);
		return final_res;
	}

	private static double rollout_onthefly(UCTNode node, List<FixedAction> fixedActions, boolean min)
	{
		if(InfinityFound)
			return 0;
		
		double succReward = 0.0;
		UCTNode next = null;
		double currentReward = 0;
		if(node.isDecision())
		{
			List<UCTNode> successors = remainingSuccessors(node, fixedActions);
			next = choseUnvisitedSucc(successors);
			if(next == null)
			{
				next = chooseSuccByUCT(node, successors);
			}
			next.increaseVisitedTimes();
			addFixedActionInLocation(fixedActions, node, next);
			double srw = ValueDouble.as(stateReward.get(node.getState())).getDouble();
			//every index of successor has the same transition reward
			double trw = ValueDouble.as(transReward.get(next.getState(), 0)).getDouble();
			currentReward = srw + trw;
			succReward = rollout_onthefly(next, fixedActions,min);
		}
		else
		{
			for(UCTNode succ : node.getSuccessors())
			{
				if(canNotReachSet.get(succ.getState()))
				{
					InfinityFound = true;
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
					succ.increaseVisitedTimes();
					double rs = succ.getProbability() * rollout_onthefly(succ, fixedActions,min);
					succReward += rs;
				}
			}
		}
		double rewardOfNode = succReward + currentReward;
		if(node.getVisitedTimes() == 0 || (!min && rewardOfNode > node.getR()) || (min && rewardOfNode < node.getR()))
		{
			node.setR(rewardOfNode);
		}
		
		return rewardOfNode;
	}
	
	private static void addFixedActionInLocation(List<FixedAction> fixedActions, UCTNode node, UCTNode next)
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
		int index = 0;
		double B = estimateB(node);
		for(int i=0;i<successors.size();i++)
		{
			UCTNode succ = successors.get(i);
			double currValue = B * Math.sqrt(Math.log(node.getVisitedTimes()) / succ.getVisitedTimes()) + succ.getR();
			if(currValue > UCTValue || UCTValue == 0)
			{
				UCTValue = currValue;
				index = i;
			}
		}
		return successors.get(index);
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
