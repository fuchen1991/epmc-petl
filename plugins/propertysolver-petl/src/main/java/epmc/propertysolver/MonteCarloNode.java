package epmc.propertysolver;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class MonteCarloNode {
	private int state;
	private boolean isDecision;
	private Map<Integer,String> actions;
	//For the original version, probability for each node is enough, because each node corresponds to only one path
	//However, if we want to reuse the graph, we need more
//	private double probability;
	private Map<Integer, Double> probabilities;
	private int visitedTimes = 0;
	private List<MonteCarloNode> successors;
	private boolean explored = false;
	private double currentReward = 0;

	public MonteCarloNode(int state, boolean isDecision) {
		this.state = state;
		this.isDecision = isDecision;
		successors = new ArrayList<MonteCarloNode>();
		actions = new HashMap<Integer, String>();
		probabilities = new HashMap<Integer, Double>();
	}

	public boolean isExplored() {
		return explored;
	}
	
	public void setExplored(boolean b) {
		this.explored = b;
	}
	
	public boolean isDecision() {
		return isDecision;
	}

	public int getState() {
		return state;
	}

	public void addSuccessor(MonteCarloNode dstNode) {
		this.successors.add(dstNode);
	}

	public List<MonteCarloNode> getSuccessors() {
		return this.successors;
	}

	public String getAction(int state) {
		return actions.get(state);
	}

	public void setAction(int state, String action) {
//		this.action = action;
		this.actions.put(state, action);
	}

	public double getProbability(int state) {
		return probabilities.get(state);
	}

	public void setProbability(int state,double probability) {
//		this.probability = probability;
		this.probabilities.put(state, probability);
	}
	
	public void increaseVisitedTimes()
	{
		this.visitedTimes += 1;
	}
	
	public int getVisitedTimes() {
		return visitedTimes;
	}

	public void setVisitedTimes(int visitedTimes) {
		this.visitedTimes = visitedTimes;
	}

	public double getCurrentReward() {
		return currentReward;
	}

	public void setCurrentReward(double currentReward) {
		this.currentReward = currentReward;
	}
}

class RolloutNode {
	private int state;
	private boolean fullExplored;
	private HashMap<String, Double> successor_values;
	
	public RolloutNode(int state) {
		this.state = state;
		successor_values = new HashMap<String, Double>();
		fullExplored =false;
	}
	
	public double getValue(String key) {
		if(successor_values.containsKey(key))
			return successor_values.get(key);
		return -1;
	}
	
	public HashMap<String, Double> getSuccessor_values() {
		return successor_values;
	}

	public boolean isFullExplored() {
		return fullExplored;
	}
	
	public void setFullExplored(boolean fullExplored) {
		this.fullExplored = fullExplored;
	}
	
	public void addSuccValue(String s, double pro) {
//		if(state == 122)
//		{
//			System.out.println("state is " + state + " key is " + s + " , value is " + (pro));
//		}

		if(successor_values.containsKey(s))
		{
			double p = successor_values.get(s);
//			if(p+pro>1)
//			{
//				System.out.println("state is " + state + " ,key is " + s + " , value is " + (p) + " and " + pro);
//				System.exit(0);
//			}
			successor_values.put(s, p+pro);
		}
		else
		{
			successor_values.put(s, pro);
		}
	}

	public void reformulateSuccValues() {
		String key = "x" + state;
		if(!successor_values.containsKey(key))
			return;
		double pro = successor_values.get(key);
		successor_values.remove(key);
		if(successor_values.size() == 0)
		{
			// a loop is detected
			successor_values.put("0", 1.0);
		}
		else
		{
			for(String s : successor_values.keySet())
			{
				double p = successor_values.get(s);
				successor_values.put(s, p/(1-pro));
			}
		}
	}
	
	public void addupSucc(HashMap<String, Double> succs, double probability) {
		for(String key : succs.keySet())
		{
			if(successor_values.containsKey(key))
			{
				double p = successor_values.get(key);
				successor_values.put(key, p+succs.get(key)*probability);
			}
			else
			{
				successor_values.put(key, succs.get(key)*probability);
			}
		}
		
//		if(state == 122)
//		{
//			System.out.println("state is " + state + " key is " + successor_values.get("1"));
//			System.out.println(probability);
//			System.exit(0);
//		}
	}
}
