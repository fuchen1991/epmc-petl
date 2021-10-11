package epmc.propertysolver;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;


public class MonteCarloNode {
	private int state;
	private boolean isDecision;
	private String action;
	private double probability;
//	private int visitedTimes = 0;
	private boolean fullExplored;
	private HashMap<String, Double> successor_values;
	private List<MonteCarloNode> successors;

	public MonteCarloNode(int state, boolean isDecision) {
		this.state = state;
		this.isDecision = isDecision;
		successor_values = new HashMap<String, Double>();
		successors = new ArrayList<MonteCarloNode>();
		fullExplored =false;
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

	public String getAction() {
		return action;
	}

	public void setAction(String action) {
		this.action = action;
	}

	public double getProbability() {
		return probability;
	}

	public void setProbability(double probability) {
		this.probability = probability;
	}
	
//	public void increaseVisitedTimes()
//	{
//		this.visitedTimes += 1;
//	}
//	
//	public int getVisitedTimes() {
//		return visitedTimes;
//	}
//
//	public void setVisitedTimes(int visitedTimes) {
//		this.visitedTimes = visitedTimes;
//	}
	
	public HashMap<String, Double> getSuccessor_values() {
		return successor_values;
	}

	public void setSuccessor_values(HashMap<String, Double> successor_values) {
		this.successor_values = successor_values;
	}

	public boolean isFullExplored() {
		return fullExplored;
	}

	public void setFullExplored(boolean fullExplored) {
		this.fullExplored = fullExplored;
	}

	public void addSuccValue(String s, double pro) {
		if(successor_values.containsKey(s))
		{
			double p = successor_values.get(s);
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
		for(String s : successor_values.keySet())
		{
			double p = successor_values.get(s);
			successor_values.put(s, p/pro);
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
	}
}
