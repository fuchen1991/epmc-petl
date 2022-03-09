package epmc.propertysolver;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
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

public class UtilInstantReward {

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
	
	private static void init(GraphExplicit gh, ModelChecker mc, NodeProperty sr)
	{
		modelChecker = mc;
		graph = gh;
		stateReward = sr;
		actionLabel = graph.getEdgeProperty(CommonProperties.TRANSITION_LABEL);
		probability = graph.getEdgeProperty(CommonProperties.WEIGHT);
//		List<Module> modules = ((ModelMAS) modelChecker.getModel()).getModelPrism().getModules();
		players = ((ModelMAS) modelChecker.getModel()).getPlayers();
        equivalenceClasses = new EquivalenceClasses(modelChecker);
//        for(Module m : modules)
//        {
//        	players.add(m.getName());
//        }
        Options options = Options.get();
        timeLimit = options.getInteger(OptionsUCT.UCT_TIME_LIMIT);
        bValueCoefficient = options.getInteger(OptionsUCT.BVALUE);
        printTimeInterval = options.getInteger(OptionsUCT.PRINT_TIME_INTERVAL);
        seed = options.getInteger(OptionsUCT.RANDOM_SEED);
        random = new Random(seed);
	}
	
	public static double[] computeProbabilities(boolean min, StateSetExplicit computeForStates, GraphExplicit gh, ModelChecker mc, int k, NodeProperty sr)
	{
		init(gh,mc,sr);
		
		int size = computeForStates.size();
		double[] resultValue = new double[size];
		for(int i=0;i<size;i++)
		{
			PropertySolverPOSGInstantReward.countMemoryUsage();
			int state = computeForStates.getExplicitIthState(i);
			resultValue[i] = exploreWhenUCT(state, min,k);
		}
		return resultValue;
	}
	
	private static double exploreWhenUCT(int state, boolean min, int k)
	{
		System.out.println("Time limit: " + timeLimit);
		System.out.println("B value Coefficient: " + bValueCoefficient);
		System.out.println("Random seed: " + seed);
		UCTNode root = constructNode(state, emptyAction, true);
		exploreSearchTreeOnTheFly(root, min);
		System.out.println("Start to rollout...");
		int rolloutTimes = 0;
		long elapsed = 0;
		StopWatch watch = new StopWatch(true);
		
		while(watch.getTimeSeconds() < timeLimit)
		{
			if(watch.getTime() - elapsed * 1000  >= printTimeInterval * 1000)
			{
				PropertySolverPOSGInstantReward.countMemoryUsage();
				elapsed += printTimeInterval;
				System.out.println("Elapsed time: " +  elapsed + "s Current result: " + root.getR()+ " rollouts: " + rolloutTimes + " nodes: " + constructedNode);
			}
			root.increaseVisitedTimes();
			rolloutTimes += 1;
			rollout_onthefly(root, k, new ArrayList<FixedAction>(),min);
		}
		
		double final_res = root.getR();
		System.out.println("============================");
		System.out.println("Final result: " + final_res);
		System.out.println("Number of rollouts: " + rolloutTimes);
		System.out.println("Number of nodes: " + constructedNode);
		return final_res;
	}

	private static double rollout_onthefly(UCTNode node, int depth, List<FixedAction> fixedActions, boolean min)
	{
		if(depth == 0)
			return ValueDouble.as(stateReward.get(node.getState())).getDouble();
		double res = 0.0;
		UCTNode next = null;
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
			res = rollout_onthefly(next,depth, fixedActions,min);
		}
		else
		{
			for(UCTNode succ : node.getSuccessors())
			{
				if(depth > 0 && !succ.isInitialized())
					exploreSearchTreeOnTheFly(succ, min);
				succ.increaseVisitedTimes();
				double rs = succ.getProbability() * rollout_onthefly(succ, depth-1, fixedActions,min);
				res += rs;
			}
		}
		if(node.getVisitedTimes() == 0 || (!min && res > node.getR()) || (min && res < node.getR()))
		{
			node.setR(res);
		}
		
		return res;
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
	
	private static UCTNode constructNode(int state, String action, boolean isDecision)
	{
		constructedNode += 1;
		UCTNode node = new UCTNode(state, action, isDecision);
		node.setVisitedTimes(0);
		node.setR(0.0);
		
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
            UCTNode succNode = constructNode(succ, nextAction, false);
            for (int index = 0; index < graph.getNumSuccessors(succ); index++)
    		{
    			int dst = graph.getSuccessorNode(succ, index);
    			double pro = ((ValueDouble) probability.get(succ, index)).getDouble();
    			UCTNode dstNode = constructNode(dst, emptyAction, true);
    			dstNode.setProbability(pro);
    			succNode.addSuccessor(dstNode);
    		}
            
            node.addSuccessor(succNode);
		}
		node.setInitialized(true);
	}
	
}
