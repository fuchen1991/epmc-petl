package epmc.propertysolver;

import java.io.File;
import java.io.FileWriter;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;

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

public class UtilApproximation {

	private static int timeLimit = 1;
	private static int depthLimit = 1;
	private static int bValueCoefficient = 1;
	private static int printTimeInterval = 1;
	private static ModelChecker modelChecker;
	private static GraphExplicit graph;
	private static List<String> players;
//	private static NodeProperty isState;
	private static EdgeProperty actionLabel;
	private static EdgeProperty probability;
	private static String emptyAction = "";
	private static BitSet oneStates;
	private static BitSet zeroStates;
	private static EquivalenceClasses equivalenceClasses;
	private static Random random;
	private static int seed = 1000;
	private static int constructedNode = 0;
	
	private static void init(GraphExplicit gh, ModelChecker mc)
	{
		modelChecker = mc;
		graph = gh;
//		isState = graph.getNodeProperty(CommonProperties.STATE);
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
        depthLimit = options.getInteger(OptionsUCT.UCT_DEPTH_LIMIT);
        bValueCoefficient = options.getInteger(OptionsUCT.BVALUE);
        printTimeInterval = options.getInteger(OptionsUCT.PRINT_TIME_INTERVAL);
        seed = options.getInteger(OptionsUCT.RANDOM_SEED);
        random = new Random(seed);
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
				//double result = firstExploreThenUCT(state, oneSet, zeroSet, min);
				double result = exploreWhenUCT(state, oneSet, zeroSet, min);
				//double result = exploreWhenUCT_rolloutOneSuccessor(state, oneSet, zeroSet, min);
				if(negate)
					resultValue[i] = 1.0 - result;
				else
					resultValue[i] = result;
			}
		}
		return resultValue;
	}
	
	private static double exploreWhenUCT(int state, BitSet oneSet, BitSet zeroSet, boolean min)
	{
		System.out.println("Depth limit: " + depthLimit);
		System.out.println("Time limit: " + timeLimit);
		System.out.println("B value Coefficient: " + bValueCoefficient);
		System.out.println("Random seed: " + seed);
		UCTNode root = constructNode(state, emptyAction, true, min);
		exploreSearchTreeOnTheFly(root, min);
		System.out.println("Start to rollout...");
		int rolloutTimes = 0;
		long elapsed = 0;
		StopWatch watch = new StopWatch(true);
		if(min)
		{
			while(watch.getTimeSeconds() < timeLimit)
			{
				//if(watch.getTimeSeconds() - elapsed >= printTimeInterval)
				if(watch.getTime() - elapsed * 1000  >= printTimeInterval * 1000)
				{
					elapsed += printTimeInterval;
					System.out.println("Elapsed time: " +  elapsed + "s Current result: " + (1 - root.getR()) + " rollouts: " + rolloutTimes + " nodes: " + constructedNode);
				}
				root.increaseVisitedTimes();
				rolloutTimes += 1;
				//rollout_min_onthefly(root, depthLimit, new ArrayList<FixedAction>(),min);
				rollout_min_onthefly_maxnotB(root, depthLimit, new ArrayList<FixedAction>(), min);
				//if(root.getR() == 0.0)
				//	break;
			}
		}
		else
		{
			while(watch.getTimeSeconds() < timeLimit)
			{
				//if(watch.getTimeSeconds() - elapsed >= printTimeInterval)
				if(watch.getTime() - elapsed * 1000  >= printTimeInterval * 1000)
				{
					//elapsed = watch.getTimeSeconds();
					elapsed += printTimeInterval;
					System.out.println("Elapsed time: " +  elapsed + "s Current result: " + root.getR()+ " rollouts: " + rolloutTimes + " nodes: " + constructedNode);
				}
				root.increaseVisitedTimes();
				rolloutTimes += 1;
				rollout_max_onthefly(root, depthLimit, new ArrayList<FixedAction>(),min);
				//if(root.getR() == 1.0)
				//	break;
			}
		}
		
		double final_res = root.getR();
		if(min)
			final_res = 1 - final_res;
		//printScheduler(root, oneSet, zeroSet);
		System.out.println("============================\nExplore all successors:");
		System.out.println("Final result: " + final_res);
		System.out.println("Number of rollouts: " + rolloutTimes);
		System.out.println("Number of nodes: " + constructedNode);
		return final_res;
	}

	private static double rollout_max_onthefly(UCTNode node, int depth, List<FixedAction> fixedActions, boolean min)
	{
		if(depth == 0)
			return 0.0;
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
			//res = rollout_max_onthefly(next,depth, addFixedAction(fixedActions, node, next),min);
			res = rollout_max_onthefly(next,depth, fixedActions,min);
		}
		else
		{
			for(UCTNode succ : node.getSuccessors())
			{
				succ.increaseVisitedTimes();
				double rs = 0.0;
				if(oneStates.get(succ.getState()))
				{
					rs = succ.getProbability();
				}
				else if(zeroStates.get(succ.getState()))
				{
					rs = 0.0;
				}
				else// if(depth > 0)
				{
					if(depth > 0 && !succ.isInitialized())
						exploreSearchTreeOnTheFly(succ, min);
					rs = succ.getProbability() * rollout_max_onthefly(succ, depth-1, fixedActions,min);
				}
				res += rs;
			}
		}
		if(res > node.getR())
		{
			if(node.isDecision())
			{
				node.setBestSucc(next);
			}
			node.setR(res);
		}
		
		return res;
	}
	
	private static double rollout_min_onthefly_maxnotB(UCTNode node, int depth, List<FixedAction> fixedActions, boolean min)
	{
		if(depth == 0)
			return 0;
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
			//res = rollout_min_onthefly(next,depth, addFixedAction(fixedActions, node, next),min);
			res = rollout_min_onthefly_maxnotB(next,depth, fixedActions,min);
		}
		else
		{
			for(UCTNode succ : node.getSuccessors())
			{
				succ.increaseVisitedTimes();
				double rs = 0;
				if(oneStates.get(succ.getState()))
				{
					rs = 0;
				}
				else if(zeroStates.get(succ.getState()))
				{
					rs = succ.getProbability();
				}
				else// if(depth > 0)
				{
					if(depth > 0 && !succ.isInitialized())
						exploreSearchTreeOnTheFly(succ, min);
					rs = succ.getProbability() * rollout_min_onthefly_maxnotB(succ, depth-1, fixedActions,min);
				}
				res += rs;
			}
		}
		if(res > node.getR())
		{
			if(node.isDecision())
			{
				node.setBestSucc(next);
			}
			node.setR(res);
		}
		
		return res;
	}
	
	private static double rollout_min_onthefly(UCTNode node, int depth, List<FixedAction> fixedActions, boolean min)
	{
		if(depth == 0)
			return -1.0;
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
			//res = rollout_min_onthefly(next,depth, addFixedAction(fixedActions, node, next),min);
			res = rollout_min_onthefly(next,depth, fixedActions,min);
		}
		else
		{
			for(UCTNode succ : node.getSuccessors())
			{
				succ.increaseVisitedTimes();
				double rs = -1 * succ.getProbability();
				if(oneStates.get(succ.getState()))
				{
					rs = -1 * succ.getProbability();
				}
				else if(zeroStates.get(succ.getState()))
				{
					rs = 0.0;
				}
				else// if(depth > 0)
				{
					if(depth > 0 && !succ.isInitialized())
						exploreSearchTreeOnTheFly(succ, min);
					rs = succ.getProbability() * rollout_min_onthefly(succ, depth-1, fixedActions,min);
				}
				res += rs;
			}
		}
		if(res > node.getR())
		{
			if(node.isDecision())
			{
				node.setBestSucc(next);
			}
			node.setR(res);
		}
		
		return res;
	}
	
//	private static List<FixedAction> addFixedAction(List<FixedAction> fixedActions, UCTNode node, UCTNode next)
//	{
//		List<FixedAction> newFixedActions = new ArrayList<FixedAction>(fixedActions);
//		String globalAction = next.getAction();
//		//String[] localActions = globalAction.split(",");
//		int state = node.getState();
//		for(int i=0;i<players.size();i++)
//		{
//			FixedAction fa = new FixedAction(players.get(i), state, globalAction);
//			if(!fixedActions.contains(fa))
//			{
//				newFixedActions.add(fa);
//			}
//		}
//		return newFixedActions;
//	}
	
	private static void addFixedActionInLocation(List<FixedAction> fixedActions, UCTNode node, UCTNode next)
	{
		String globalAction = next.getAction();
		//String[] localActions = globalAction.split(",");
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
	
//	private String fixedActionToString(List<FixedAction> actions)
//	{
//		Set<String> all = new HashSet<String>();
//		for(FixedAction fa : actions)
//		{
//			BitSet bs = equivalenceClasses.getClassFor(fa.player, fa.state);
//			String str = fa.player + "_" + bs.toString() + "_" + fa.action;
//			all.add(str);
//		}
//		List<String> strList = new ArrayList<String>(all);
//		Collections.sort(strList);
//		StringBuilder builder = new StringBuilder();
//		for(String s : strList)
//		{
//			builder.append(s);
//		}
//		return builder.toString();
//	}
	
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
		if(node.getR() < 0)
		{
			res = 1 + node.getR();
		}
		return res * bValueCoefficient;
	}
	
	private static UCTNode constructNode(int state, String action, boolean isDecision, boolean min)
	{
		constructedNode += 1;
		UCTNode node = new UCTNode(state, action, isDecision);
		node.setVisitedTimes(0);
		if(min)
			node.setR(-1.0);
		else
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
	
	private static double exploreWhenUCT_rolloutOneSuccessor(int state, BitSet oneSet, BitSet zeroSet, boolean min)
	{
		System.out.println("Depth limit: " + depthLimit);
		System.out.println("Time limit: " + timeLimit);
		System.out.println("B value Coefficient: " + bValueCoefficient);
		System.out.println("Random seed: " + seed);
		UCTNode root = constructNode(state, emptyAction, true, min);
		exploreSearchTreeOnTheFly(root, min);
		System.out.println("Start to rollout...");
		int rolloutTimes = 0;
		long elapsed = 0;
		StopWatch watch = new StopWatch(true);
		if(min)
		{
			while(watch.getTimeSeconds() < timeLimit)
			{
				if(watch.getTimeSeconds() - elapsed >= printTimeInterval)
				{
					elapsed = watch.getTimeSeconds();
					System.out.println("Remaining time: " + (timeLimit - watch.getTimeSeconds()) + "s" + " Current rollout: " + rolloutTimes + " Current result: " + root.getR()+ " Current nodes: " + constructedNode);
				}
				root.increaseVisitedTimes();
				rolloutTimes += 1;
				rollout_min_onthefly_oneSuccessor(root, depthLimit, new ArrayList<FixedAction>(),min);
				if(root.getR() == 0.0)
					break;
			}
		}
		else
		{
			while(watch.getTimeSeconds() < timeLimit)
			{
				if(watch.getTimeSeconds() - elapsed >= printTimeInterval)
				{
					elapsed = watch.getTimeSeconds();
					System.out.println("Remaining time: " + (timeLimit - watch.getTimeSeconds()) + "s" + " Current rollout: " + rolloutTimes + " Current result: " + root.getR()+ " Current nodes: " + constructedNode);
				}
				root.increaseVisitedTimes();
				rolloutTimes += 1;
				rollout_max_onthefly_oneSuccessor(root, depthLimit, new ArrayList<FixedAction>(),min);
				if(root.getR() == 1.0)
					break;
			}
		}
		
		printScheduler(root, oneSet, zeroSet);
		System.out.println("============================\nExplore one successor:");
		System.out.println("Times of rollouts: " + rolloutTimes);
		System.out.println("Number of nodes: " + constructedNode);
		return root.getR();
	}
	
	private static double rollout_max_onthefly_oneSuccessor(UCTNode node, int depth, List<FixedAction> fixedActions, boolean min)
	{
		if(depth == 0)
			return 0.0;
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
			res = rollout_max_onthefly_oneSuccessor(next,depth, fixedActions,min);
		}
		else
		{
			int ii = random.nextInt(node.getSuccessors().size());
			UCTNode succ = node.getSuccessors().get(ii);
			succ.increaseVisitedTimes();
			//System.out.println(node.getSuccessors().size());
//			if(oneStates.get(succ.getState()))
//			{
//				System.out.println(succ.getState());
//			}
			if( !(oneStates.get(succ.getState()) || zeroStates.get(succ.getState())))
			{
				if(depth > 0 && !succ.isInitialized())
					exploreSearchTreeOnTheFly(succ, min);
				rollout_max_onthefly_oneSuccessor(succ, depth-1, fixedActions,min);
			}
			res = addupSuccessorProbability(node, fixedActions,false);
		}
		List<FixedAction> newFixedActions = new ArrayList<FixedAction>(fixedActions);
		if(node.getRByFixedActions(newFixedActions) < res)
			node.setRByFixedActions(newFixedActions, res);
		
		if(res > node.getR())
		{
			if(node.isDecision())
			{
				node.setBestSucc(next);
			}
			node.setR(res);
		}
		return res;
	}
	
	private static double addupSuccessorProbability(UCTNode node, List<FixedAction> fixedActions, boolean min)
	{
		double res = 0.0;
		for(UCTNode iter : node.getSuccessors())
		{
			double rs = 0.0;
			if(oneStates.get(iter.getState()))
			{
				if(min)
					rs = -1;
				else
					rs = 1;
				//System.out.println(iter.getState());
			}
			else if(zeroStates.get(iter.getState()))
			{
				rs = 0.0;
			}
			else
			{
				rs = iter.getRByFixedActions(fixedActions);
				if(rs == -1 && !min)
				{
					rs = 0.0;
				}
			}
			res += iter.getProbability() * rs;
		}
		return res;
	}
	
	private static double rollout_min_onthefly_oneSuccessor(UCTNode node, int depth, List<FixedAction> fixedActions, boolean min)
	{
		if(depth == 0)
			return -1;
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
			res = rollout_min_onthefly_oneSuccessor(next,depth, fixedActions,min);
		}
		else
		{
			UCTNode succ = node.getSuccessors().get(random.nextInt(node.getSuccessors().size()));
			succ.increaseVisitedTimes();
			if( !(oneStates.get(succ.getState()) || zeroStates.get(succ.getState())))
			{
				if(depth > 0 && !succ.isInitialized())
					exploreSearchTreeOnTheFly(succ, min);
				rollout_min_onthefly_oneSuccessor(succ, depth-1, fixedActions,min);
			}
			res = addupSuccessorProbability(node, fixedActions,true);
		}
		List<FixedAction> newFixedActions = new ArrayList<FixedAction>(fixedActions);
		if(node.getRByFixedActions(newFixedActions) < res)
			node.setRByFixedActions(newFixedActions, res);
		
		if(res > node.getR())
		{
			if(node.isDecision())
			{
				node.setBestSucc(next);
			}
			node.setR(res);
		}
		return res;
	}
	
	private static void printScheduler(UCTNode node, BitSet oneSet, BitSet zeroSet)
	{
		//Only for debuging
		//Not correct, because it doesn't consider the uniform constraints when printing
		List<UCTNode> list = new ArrayList<UCTNode>();
		list.add(node);
		p("Start to print the best scheduler:");
		while(!list.isEmpty())
		{
			UCTNode curr = list.remove(0);
			if(curr.isDecision())
			{
				if(curr.getBestSucc() != null)
				{
					p("state: " + curr.getState() + " choose: " + curr.getBestSucc().getAction() + " to state: " + curr.getBestSucc().getState());
					list.add(curr.getBestSucc());
				}
			}
			else
			{
				for(UCTNode succ : curr.getSuccessors())
				{
					p("pro state: " + curr.getState() + " to state: " + succ.getState() + " with pro: " + succ.getProbability() + " (oneState? " + oneSet.get(succ.getState()) + " zeroState? " + zeroSet.get(succ.getState()) + ")");
					list.add(succ);
				}
			}
		}
	}
	
	private static void p(String str)
	{
		System.out.println(str);
	}
	private static void p(double str)
	{
		System.out.println(str);
	}

	private static void pf(String str)
    {
    	FileWriter out = null;
		try {
			out = new FileWriter(new File("//home//fuchen//Desktop//graph"));
			out.write(str);
			out.close();
		} catch (Exception e) {
			e.printStackTrace();
		}
    }
	
//	private static double firstExploreThenUCT(int state, BitSet oneSet, BitSet zeroSet, boolean min)
//	{
//		//depthLimit = unKnown.cardinality();
//		System.out.println("Depth limit: " + depthLimit);
//		StopWatch wh = new StopWatch(true);
//		UCTNode root = exploreSearchTree(state, emptyAction, true, depthLimit, min);
//		System.out.println("Explore time: " + wh.getTimeSeconds() + " s");
//		System.out.println("Start to rollout...");
//		int rolloutTimes = 0;
//		long elapsed = 0;
//		StopWatch watch = new StopWatch(true);
//		if(min)
//		{
//			while(watch.getTimeSeconds() < timeLimit)
//			{
//				if(watch.getTimeSeconds() - elapsed > printTimeInterval)
//				{
//					elapsed = watch.getTimeSeconds();
//					System.out.println("Remaining time: " + (timeLimit - watch.getTimeSeconds()) + " s");
//				}
//				root.increaseVisitedTimes();
//				rolloutTimes += 1;
//				rollout_min(root, depthLimit, new ArrayList<FixedAction>());
//				if(root.getR() == 0.0)
//					break;
//			}
//		}
//		else
//		{
//			while(watch.getTimeSeconds() < timeLimit)
//			{
//				if(watch.getTimeSeconds() - elapsed > printTimeInterval)
//				{
//					elapsed = watch.getTimeSeconds();
//					System.out.println("Remaining time: " + (timeLimit - watch.getTimeSeconds()) + " s");
//				}
//				root.increaseVisitedTimes();
//				rolloutTimes += 1;
//				rollout_max(root, depthLimit, new ArrayList<FixedAction>());
//				if(root.getR() == 1.0)
//					break;
//			}
//		}
//		
//		System.out.println("Times of rollouts: " + rolloutTimes);
//		printScheduler(root, oneSet, zeroSet);
//		
//		return root.getR();
//	}
	
//	private static double rollout_max(UCTNode node, int depth, List<FixedAction> fixedActions)
//	{
//		if(depth == 0)
//			return 0.0;
//		double res = 0.0;
//		UCTNode next = null;
//		if(node.isDecision())
//		{
//			List<UCTNode> successors = remainingSuccessors(node, fixedActions);
//			next = choseUnvisitedSucc(successors);
//			if(next == null)
//			{
//				next = chooseSuccByUCT(node, successors);
//			}
//			next.increaseVisitedTimes();
//			res = rollout_max(next,depth, addFixedAction(fixedActions, node, next));
//		}
//		else
//		{
//			for(UCTNode succ : node.getSuccessors())
//			{
//				succ.increaseVisitedTimes();
//				double rs = 0.0;
//				if(oneStates.get(succ.getState()))
//				{
//					rs = succ.getProbability();
//				}
//				else if(zeroStates.get(succ.getState()))
//				{
//					rs = 0.0;
//				}
//				else// if(depth > 0)
//				{
//					rs = succ.getProbability() * rollout_max(succ, depth-1, fixedActions);
//				}
//				res += rs;
//			}
//		}
//		if(res > node.getR())
//		{
//			if(node.isDecision())
//			{
//				node.setBestSucc(next);
//			}
//			node.setR(res);
//		}
////		else
////			res = node.getR();
//		return res;
//	}
//	
//	private static double rollout_min(UCTNode node, int depth, List<FixedAction> fixedActions)
//	{
//		if(depth == 0)
//			return 1.0;
//		double res = 0.0;
//		UCTNode next = null;
//		if(node.isDecision())
//		{
//			List<UCTNode> successors = remainingSuccessors(node, fixedActions);
//			next = choseUnvisitedSucc(successors);
//			if(next == null)
//			{
//				next = chooseSuccByUCT(node, successors);
//			}
//			next.increaseVisitedTimes();
//			res = rollout_min(next,depth, addFixedAction(fixedActions, node, next));
//		}
//		else
//		{
//			for(UCTNode succ : node.getSuccessors())
//			{
//				succ.increaseVisitedTimes();
//				double rs = succ.getProbability();
//				if(oneStates.get(succ.getState()))
//				{
//					rs = succ.getProbability();
//				}
//				else if(zeroStates.get(succ.getState()))
//				{
//					rs = 0.0;
//				}
//				else// if(depth > 0)
//				{
//					rs = succ.getProbability() * rollout_min(succ, depth-1, fixedActions);
//				}
//				res += rs;
//			}
//		}
//		if(res < node.getR())
//		{
//			if(node.isDecision())
//			{
//				node.setBestSucc(next);
//			}
//			node.setR(res);
//		}
////		else
////			res = node.getR();
//		return res;
//	}
	
//	private static UCTNode exploreSearchTree(int state, String action, boolean isDecision, int depth, boolean min)
//	{
//		UCTNode node = new UCTNode(state, action, isDecision);
//		node.setVisitedTimes(0);
//		if(min)
//			node.setR(1.0);
//		else
//			node.setR(0.0);
//		
//		if(isState.getBoolean(state))
//		{
//			//decision node
//			//for decision nodes, one should not use 'action'
//			if(depth <= 0)
//				return node;
//			for (int iter = 0; iter < graph.getNumSuccessors(state); iter++)
//    		{
//    			int succ = graph.getSuccessorNode(state, iter);
//    			Action ac = actionLabel.getObject(state, iter);
//                String nextAction = ac.getName();
//                UCTNode succNode = exploreSearchTree(succ, nextAction, false, depth, min);
//                node.addSuccessor(succNode);
//    		}
//		}
//		else
//		{
//			//chance node
//			for (int iter = 0; iter < graph.getNumSuccessors(state); iter++)
//    		{
//    			int succ = graph.getSuccessorNode(state, iter);
//    			double pro = ((ValueDouble) probability.get(state, iter)).getDouble();
//    			UCTNode succNode = exploreSearchTree(succ, emptyAction, true, depth-1, min);
//    			succNode.setProbability(pro);
//                node.addSuccessor(succNode);
//    		}
//		}
//		
//		return node;
//	}
}
