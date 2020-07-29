package epmc.propertysolver;

import static epmc.value.UtilValue.newValue;

import java.io.File;
import java.io.FileWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import epmc.algorithms.explicit.ComponentsExplicit;
import epmc.algorithms.explicit.EndComponents;
import epmc.constraintsolver.ConstraintSolver;
import epmc.constraintsolver.ConstraintSolverConfiguration;
import epmc.constraintsolver.ConstraintSolverResult;
import epmc.constraintsolver.Direction;
import epmc.constraintsolver.Feature;
import epmc.constraintsolver.smtlib.ConstraintSolverSMTLib;
import epmc.error.Positional;
import epmc.expression.Expression;
import epmc.expression.standard.DirType;
import epmc.expression.standard.ExpressionLiteral;
import epmc.expression.standard.ExpressionOperator;
import epmc.expression.standard.ExpressionQuantifier;
import epmc.expression.standard.ExpressionTemporalFinally;
import epmc.expression.standard.ExpressionTemporalGlobally;
import epmc.expression.standard.ExpressionTemporalRelease;
import epmc.expression.standard.ExpressionTemporalUntil;
import epmc.expression.standard.TimeBound;
import epmc.expression.standard.evaluatorexplicit.UtilEvaluatorExplicit;
import epmc.graph.CommonProperties;
import epmc.graph.Semantics;
import epmc.graph.SemanticsContinuousTime;
import epmc.graph.SemanticsDTMC;
import epmc.graph.SemanticsMDP;
import epmc.graph.StateMap;
import epmc.graph.StateSet;
import epmc.graph.UtilGraph;
import epmc.graph.explicit.EdgeProperty;
import epmc.graph.explicit.GraphExplicit;
import epmc.graph.explicit.NodeProperty;
import epmc.graph.explicit.StateMapExplicit;
import epmc.graph.explicit.StateSetExplicit;
import epmc.graphsolver.GraphSolverConfigurationExplicit;
import epmc.graphsolver.UtilGraphSolver;
import epmc.graphsolver.objective.GraphSolverObjectiveExplicitBounded;
import epmc.graphsolver.objective.GraphSolverObjectiveExplicitBoundedReachability;
import epmc.graphsolver.objective.GraphSolverObjectiveExplicitUnboundedReachability;
import epmc.modelchecker.EngineExplicit;
import epmc.modelchecker.ModelChecker;
import epmc.modelchecker.PropertySolver;
import epmc.operator.Operator;
import epmc.operator.OperatorGt;
import epmc.operator.OperatorNot;
import epmc.operator.OperatorSet;
import epmc.operator.OperatorSubtract;
import epmc.petl.model.ModelMAS;
import epmc.prism.model.Module;
import epmc.util.BitSet;
import epmc.util.StopWatch;
import epmc.util.UtilBitSet;
import epmc.value.ContextValue;
import epmc.value.OperatorEvaluator;
import epmc.value.Type;
import epmc.value.TypeAlgebra;
import epmc.value.TypeArray;
import epmc.value.TypeBoolean;
import epmc.value.TypeDouble;
import epmc.value.TypeInteger;
import epmc.value.TypeReal;
import epmc.value.TypeWeight;
import epmc.value.UtilValue;
import epmc.value.Value;
import epmc.value.ValueAlgebra;
import epmc.value.ValueArray;
import epmc.value.ValueArrayAlgebra;
import epmc.value.ValueBoolean;
import epmc.value.ValueDouble;
import epmc.value.ValueInteger;
import epmc.value.ValueObject;
import epmc.jani.model.Action;

public class PropertySolverExplicitPCTLUntilUniform implements PropertySolver {
	public final static String IDENTIFIER = "pctl-explicit-until-uniform";
    private ModelChecker modelChecker;
    private GraphExplicit graph;
    private StateSetExplicit computeForStates;
    private Expression property;
    private StateSet forStates;
    private boolean convert2Quadratic = false;
    private boolean usingF = true;
    private boolean fIsReal = false;
    private boolean pIsReal = false;
    
	@Override
	public boolean canHandle() {
		assert property != null;
        if (!(modelChecker.getEngine() instanceof EngineExplicit)) {
            return false;
        }
        Semantics semantics = modelChecker.getModel().getSemantics();
        if (!SemanticsDTMC.isDTMC(semantics) && !SemanticsMDP.isMDP(semantics)) {
            return false;
        }
        
        if (!(property instanceof ExpressionQuantifier)) {
            return false;
        } 
        //The model should be a mas
        if (!(modelChecker.getModel() instanceof ModelMAS)) {
            return false;
        }
        
        handleSimplePCTLExtensions();
        
        ExpressionQuantifier propertyQuantifier = ExpressionQuantifier.as(property);
        if (!UtilPETL.isPCTLPath(propertyQuantifier.getQuantified())) {
            return false;
        }
        if (!UtilPETL.isPCTLPathUntil(propertyQuantifier.getQuantified())) {
            return false;
        }
        
        Set<Expression> inners = UtilPETL.collectPCTLInner(propertyQuantifier.getQuantified());
        StateSet allStates = UtilGraph.computeAllStatesExplicit(modelChecker.getLowLevel());
        for (Expression inner : inners) {
            modelChecker.ensureCanHandle(inner, allStates);
        }
        if (allStates != null) {
            allStates.close();
        }
        return true;
	}
	
	@Override
	public StateMap solve() {
		assert property != null;
        assert forStates != null;
        assert property instanceof ExpressionQuantifier;
		StateSetExplicit forStatesExplicit = (StateSetExplicit) forStates;
        graph.explore(forStatesExplicit.getStatesExplicit());
        
        //printFile(graph.toString().replaceAll("\"name", "name").replaceAll("\":\"", ":").replaceAll("\"}", "}"));    
        
        ExpressionQuantifier propertyQuantifier = (ExpressionQuantifier) property;
        Expression quantifiedProp = propertyQuantifier.getQuantified();
        DirType dirType = ExpressionQuantifier.computeQuantifierDirType(propertyQuantifier);
        StateMap result = doSolve(quantifiedProp, forStates, dirType.isMin());
        if (!propertyQuantifier.getCompareType().isIs()) {
            StateMap compare = modelChecker.check(propertyQuantifier.getCompare(), forStates);
            Operator op = propertyQuantifier.getCompareType().asExOpType();
            assert op != null;
            result = result.applyWith(op, compare);
        }
        return result;
	}

	private StateMap doSolve(Expression property, StateSet states, boolean min) {
		boolean negate;
        if (isNot(property)) {
            ExpressionOperator propertyOperator = (ExpressionOperator) property;
            property = propertyOperator.getOperand1();
            negate = true;
            min = !min;
        } else if (isRelease(property)) {
        	ExpressionTemporalRelease pathTemporal = ExpressionTemporalRelease.as(property);
            Expression left = pathTemporal.getOperandLeft();
            Expression right = pathTemporal.getOperandRight();
            property = new ExpressionTemporalUntil.Builder()
                    .setOperandLeft(not(left))
                    .setOperandRight(not(right))
                    .setTimeBound(pathTemporal.getTimeBound())
                    .setPositional(property.getPositional())
                    .build();
            min = !min;
            negate = true;
        } else if (isFinally(property)) {
            ExpressionTemporalFinally pathTemporal = ExpressionTemporalFinally.as(property);
            Expression left = ExpressionLiteral.getTrue();
            Expression right = pathTemporal.getOperand();
            property = new ExpressionTemporalUntil.Builder()
                    .setOperandLeft(left)
                    .setOperandRight(right)
                    .setTimeBound(pathTemporal.getTimeBound())
                    .setPositional(property.getPositional())
                    .build();
            negate = false;
        } else if (isGlobally(property)) {
            ExpressionTemporalGlobally pathTemporal = ExpressionTemporalGlobally.as(property);
            Expression left = ExpressionLiteral.getTrue();
            Expression right = not(pathTemporal.getOperand());
            property = new ExpressionTemporalUntil.Builder()
                    .setOperandLeft(left)
                    .setOperandRight(right)
                    .setTimeBound(pathTemporal.getTimeBound())
                    .setPositional(property.getPositional())
                    .build();
            min = !min;
            negate = true;
        } else {
            negate = false;
        }
        StateSet allStates = UtilGraph.computeAllStatesExplicit(modelChecker.getLowLevel());
        ExpressionTemporalUntil propertyTemporal = ExpressionTemporalUntil.as(property);
        Expression op1 = propertyTemporal.getOperandLeft();
        StateMapExplicit innerResult1 = (StateMapExplicit) modelChecker.check(op1, allStates);
        UtilGraph.registerResult(graph, op1, innerResult1);
        Expression op2 = propertyTemporal.getOperandRight();
        StateMapExplicit innerResult2 = (StateMapExplicit) modelChecker.check(op2, allStates);
        UtilGraph.registerResult(graph, op2, innerResult2);
        allStates.close();
        this.computeForStates = (StateSetExplicit) states;
        return solve(propertyTemporal, min, negate, innerResult1, innerResult2);
	}
	
	private StateMap solve(ExpressionTemporalUntil pathTemporal, boolean min, boolean negate, StateMapExplicit innerLeft, StateMapExplicit innerRight) {
		assert pathTemporal != null;
		Semantics semantics = modelChecker.getModel().getSemantics();
        if (SemanticsDTMC.isDTMC(semantics)) {
            return solveDTMC(pathTemporal, min, negate, innerLeft, innerRight);
        }

        TypeAlgebra typeWeight = TypeWeight.get();    
        BitSet allNodes = UtilBitSet.newBitSetUnbounded();
        allNodes.set(0, graph.getNumNodes(), true);

        ValueAlgebra transValue = typeWeight.newValue();
        OperatorEvaluator set = ContextValue.get().getEvaluator(OperatorSet.SET, typeWeight, typeWeight);
        set.apply(transValue, UtilValue.newValue(typeWeight, 0));

        BitSet zeroSet = UtilBitSet.newBitSetUnbounded();
        BitSet oneSet = UtilBitSet.newBitSetUnbounded();
        NodeProperty stateProp = graph.getNodeProperty(CommonProperties.STATE);
        ValueBoolean valueLeft = TypeBoolean.get().newValue();
        ValueBoolean valueRight = TypeBoolean.get().newValue();
        for (int i = 0; i < innerLeft.size(); i++) {
            int state = innerLeft.getExplicitIthState(i);
            if (!stateProp.getBoolean(state)) {
                continue;
            }
            innerLeft.getExplicitIthValue(valueLeft, i);
            innerRight.getExplicitIthValue(valueRight, i);
            boolean left = valueLeft.getBoolean();
            boolean right = valueRight.getBoolean();
            if (!left && !right) {
                zeroSet.set(state);
            } else if (right) {
                oneSet.set(state);
            }
        }
        BitSet unKnown = computeUnKnownStates(oneSet, zeroSet);
        //System.out.println(graph.toString().replaceAll("\"name", "name").replaceAll("\":\"", ":").replaceAll("\"}", "}"));

        ConstraintSolver solver = setBasicConstraints(unKnown,oneSet,zeroSet);
        double[] resultValue = computeProbabilities(solver, oneSet, zeroSet, min, negate,unKnown);

        Type type = TypeDouble.get();
        ValueArray resultValues = UtilValue.newArray(type.getTypeArray(), computeForStates.size());
        for (int stateNr = 0; stateNr < computeForStates.size(); stateNr++) {
            ValueDouble value = (ValueDouble) type.newValue();
            value.set(resultValue[stateNr]);
            resultValues.set(value, stateNr);
        }

		return UtilGraph.newStateMap(computeForStates.clone(), resultValues);
	}
	
	private double[] computeProbabilities(ConstraintSolver solver, BitSet oneSet, BitSet zeroSet, boolean min, boolean negate, BitSet unKnown)
	{
		int size = this.computeForStates.size();
		double[] resultValue = new double[size];
        
		System.out.println("Number of transitions:" + computeNumberOfEdges());
		
		if(!min)
		{
			if(!usingF)
			{
				List<String> constraints = getAllConstraintsForLoops(unKnown);
				for(String constraint : constraints)
				{
					//System.out.println(constraint.length());
					solver.addConstraint(UtilPETL.parseExpression(constraint));
				}
			}
			else
			{
				addConstraintsUsingNewVariables(solver, unKnown, oneSet, zeroSet);
			}
		}
		
		System.out.println("Number of variables:" + ((ConstraintSolverSMTLib)solver).getNumberOfVariables());
		System.out.println("Number of constraints:" + ((ConstraintSolverSMTLib)solver).getNumberOfConstraints());
		
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
				if(min)
				{
					double val = compuetMinProbability(solver,state);
					if(val <= 1.0)
					{
						if(negate)
							resultValue[i] = 1 - val;
						else
							resultValue[i] = val;
					}
					else
					{
						if(((ExpressionQuantifier) property).getCompareType().isIs())
						{
							System.out.println("Well, z3 can not solve this and the program will terminate ...");
							System.exit(0);
						}
						
						System.out.println("TODO: add constraints");
						System.exit(0);
					}
				}
				else
				{
					double val = compuetMaxProbability(solver,state, unKnown);
					if(val <= 1.0)
					{
						if(negate)
							resultValue[i] = 1 - val;
						else
							resultValue[i] = val;
					}
					else
					{
						if(((ExpressionQuantifier) property).getCompareType().isIs())
						{
							System.out.println("Well, z3 can not solve this and the program will terminate ...");
							System.exit(0);
						}
						
						System.out.println("TODO: add constraints");
						System.exit(0);
					}
				}
			}
		}
		return resultValue;
	}
	
	private double compuetMinProbability(ConstraintSolver solver, int state)
	{
		solver.setDirection(Direction.MIN);
    	solver.setObjective(UtilPETL.parseExpression("x" + state));
    	
    	StopWatch watch = new StopWatch(true);
    	System.out.println("Call z3 to compute the minimal probability ...");
    	ConstraintSolverResult result = solver.solve();
    	System.out.println("Time required by z3: " + watch.getTimeSeconds() + " seconds");
    	
    	solver.setObjective(null);
    	
    	if(result.equals(ConstraintSolverResult.UNSAT) || result.equals(ConstraintSolverResult.UNKNOWN))
    	{
    		System.out.println("z3 cannot compute the minimal probability for this problem");
    		return 2;
    	}
		return ((ValueDouble)solver.getResultVariablesValues()[state]).getDouble();
	}
	
	private double compuetMaxProbability(ConstraintSolver solver, int state, BitSet unKnown)
	{
		solver.setDirection(Direction.MAX);
    	solver.setObjective(UtilPETL.parseExpression("x" + state));
    	
    	StopWatch watch = new StopWatch(true);
    	System.out.println("Call z3 to compute the maximal probability ...");
    	ConstraintSolverResult result = solver.solve();
    	System.out.println("Time required by z3: " + watch.getTimeSeconds() + " seconds");
    	
    	solver.setObjective(null);
    	
    	if(result.equals(ConstraintSolverResult.UNSAT) || result.equals(ConstraintSolverResult.UNKNOWN))
    	{
    		System.out.println("z3 cannot compute the maximal probability for this problem");
    		return 2;
    	}
		return ((ValueDouble)solver.getResultVariablesValues()[state]).getDouble();
	}
	
	private void addConstraintsUsingNewVariables(ConstraintSolver solver, BitSet unKnown, BitSet oneSet, BitSet zeroSet)
	{
		NodeProperty stateProp = graph.getNodeProperty(CommonProperties.STATE);
		int nodeNum = graph.getNumNodes();
		int upper = graph.computeNumStates() - zeroSet.cardinality();
		TypeInteger typeInteger = TypeInteger.get();
		TypeReal typeReal = TypeReal.get();
        for(int i=0;i<nodeNum;i++)
        {
        	if(stateProp.getBoolean(i))
        	{
        		if(!fIsReal)
        			solver.addVariable("f"+i, typeInteger, newValue(typeInteger, 0),newValue(typeInteger, upper));
        		else
        		{
        			solver.addVariable("f"+i, typeInteger, newValue(typeReal, 0),newValue(typeReal, upper));
        			solver.addConstraint(UtilPETL.parseExpression("f" + i + "<1 => f" + i + " = 0"));
        		}
        	}
        }
        
        List<String> players = new ArrayList<String>();
        List<Module> modules = ((ModelMAS) modelChecker.getModel()).getModelPrism().getModules();
        for(Module m : modules)
        {
        	players.add(m.getName());
        }
        
        for(int state=oneSet.nextSetBit(0);state>=0 && state<nodeNum;state=oneSet.nextSetBit(state+1))
        {
        	solver.addConstraint(UtilPETL.parseExpression("f" + state + "=1"));
        }
        for(int state=zeroSet.nextSetBit(0);state>=0 && state<nodeNum;state=zeroSet.nextSetBit(state+1))
        {
        	solver.addConstraint(UtilPETL.parseExpression("f" + state + "=0"));
        }
        for(int state=unKnown.nextSetBit(0);state>=0 && state<nodeNum;state=unKnown.nextSetBit(state+1))
        {
        	solver.addConstraint(UtilPETL.parseExpression("!(f" + state + "=1)"));
        	solver.addConstraint(UtilPETL.parseExpression("f" + state + "=0 => x" + state + "=0"));
        	StringBuilder builder = new StringBuilder();
        	StringBuilder builderForSec = new StringBuilder();
        	builder.append("f" + state + ">1 =>");
        	builderForSec.append("f" + state + "=0 <=>");
        	
        	int numSucc = graph.getNumSuccessors(state);
        	Map<Integer, List<String>> stateToActions = new HashMap<Integer, List<String>>();
        	Map<Integer, List<String>> stateToProba = new HashMap<Integer, List<String>>();
        	for(int succIter = 0;succIter<numSucc;succIter++)
        	{
        		EdgeProperty label = graph.getEdgeProperty(CommonProperties.TRANSITION_LABEL);
                Value value = label.get(state, succIter);
                Action ac = (Action) ((ValueObject)value).getObject();
                String globalAction = ac.getName();
                
        		int proNode = graph.getSuccessorNode(state, succIter);
        		int realNumSucc = graph.getNumSuccessors(proNode);
        		for(int realSuccIter=0;realSuccIter<realNumSucc;realSuccIter++)
        		{
        			EdgeProperty weight = graph.getEdgeProperty(CommonProperties.WEIGHT);
        			String pro = weight.get(proNode, realSuccIter).toString();
        			int realSucc = graph.getSuccessorNode(proNode, realSuccIter);
        			
        			List<String> actions = stateToActions.get(realSucc);
        			List<String> probas = stateToProba.get(realSucc);
        			if(actions==null)
        			{
        				actions= new ArrayList<String>();
        				probas = new ArrayList<String>();
        			}
        			
    				actions.add(globalAction);
    				probas.add(pro);
    				stateToActions.put(realSucc, actions);
    				stateToProba.put(realSucc, probas);
        		}
        	}
        	int help = 0;
        	for(int succState : stateToActions.keySet())
        	{
        		if(help > 0)
        		{
        			builder.append("|");
        			builderForSec.append("&");
        		}
        		help++;
        		
        		builder.append("(");
        		builderForSec.append("(");
        		List<String> actions = stateToActions.get(succState);
        		List<String> probas = stateToProba.get(succState);
        		builder.append("f" + state + "=f" + succState + "+1 & (");
        		builderForSec.append("(f" + succState + "=0 & (");
        		
        		StringBuilder builderHelp = new StringBuilder();
        		for(int iter = 0;iter<actions.size();iter++)
        		{
        			if(iter>0)
        			{
        				builder.append("|");
        				builderHelp.append("+");
        			}
        			String[] action = actions.get(iter).split(",");
        			String proba = probas.get(iter);
        			for(int playerIndex=0;playerIndex<players.size();playerIndex++)
        			{
        				String player = players.get(playerIndex);
        				BitSet bitSet = UtilPETL.getClassFor(player, state);
        				
        				if(!convert2Quadratic)
            			{
            				builder.append("p" + playerIndex + bitSet2String(bitSet) + action[playerIndex] + "*");
            				builderHelp.append("p" + playerIndex + bitSet2String(bitSet) + action[playerIndex] + "*");
            			}
            			else
            			{
            				System.out.println("Now, it's not finished");
            				System.exit(0);
            			}
        			}
        			builder.append(proba + ">0");
        			builderHelp.append(proba);
        		}
        		builderForSec.append(builderHelp.toString() + ">0 )) | ( " + builderHelp.toString() + ")=0)");
        		builder.append("))");
        	}
        	solver.addConstraint(UtilPETL.parseExpression(builder.toString()));
        	solver.addConstraint(UtilPETL.parseExpression(builderForSec.toString()));
        }   
	}
	
	
	private List<String> getAllConstraintsForLoops(BitSet unKnown)
	{
		List<String> constraints = new ArrayList<String>();
		ComponentsExplicit components = new ComponentsExplicit();
		EndComponents endComponents = components.endComponents(graph,true);
		for (BitSet scc = endComponents.next();scc != null; scc = endComponents.next())
		{
			if(!checkSubset(scc,unKnown))
				continue;
			
			computeConstraintsForAllEndComponents(constraints, scc);
		}
		return constraints;
	}
	
	private void computeConstraintsForAllEndComponents(List<String> constraints, BitSet scc)
	{
		int size = 0;
		int numNodes = graph.getNumNodes();
		NodeProperty stateProp = graph.getNodeProperty(CommonProperties.STATE);
		List<Integer> states = new ArrayList<Integer>();
		for(int state = scc.nextSetBit(0);state>=0 && state<numNodes;state=scc.nextSetBit(state+1))
		{
			if(stateProp.getBoolean(state))
			{
				states.add(state);
				size++;
			}
		}
		generateConstraint(constraints, new ArrayList<Integer>(), states, 0, size,scc);
	}
	
	private void generateConstraint(List<String> constraints, List<Integer> currStates, List<Integer> states, int index, int size, BitSet scc)
	{
		if(index < size)
		{
			List<Integer> newCurr = new ArrayList<Integer>(currStates);
			newCurr.add(states.get(index));
			generateConstraint(constraints, newCurr, states, index+1, size,scc);
			generateConstraint(constraints, currStates, states, index+1, size,scc);
		}
		else
		{
			if(!crossReach(currStates, scc))
				return;
			
			int numState = currStates.size();
			if(numState == 0)
				return;
			
			int[] stateIndex = new int[numState];
			int sIndex = 0;
			List<List<String>> actions = new ArrayList<List<String>>();
			for(int state : currStates)
			{
				stateIndex[sIndex] = state;
				List<String> ac = new ArrayList<String>();
				sIndex++;
				int numSucc = graph.getNumSuccessors(state);
				for(int succIter=0;succIter<numSucc;succIter++)
				{
					int succNode = graph.getSuccessorNode(state, succIter);
					if(!scc.get(succNode))
						continue;
					int numRealSucc = graph.getNumSuccessors(succNode);
					boolean skip = false;
					for(int realSuccIter=0;realSuccIter<numRealSucc;realSuccIter++)
					{
						int realSucc = graph.getSuccessorNode(succNode, realSuccIter);
						if(numRealSucc == 1 && realSucc==state && numState!=1)
						{
							skip = true;
							break;
						}
						if(!currStates.contains(realSucc))
						{
							skip = true;
							break;
						}
					}
					if(!skip)
					{
						EdgeProperty label = graph.getEdgeProperty(CommonProperties.TRANSITION_LABEL);
	                    Value value = label.get(state, succIter);
	                    Action action = (Action) ((ValueObject)value).getObject();
	                    ac.add(action.getName());
					}
				}
				if(ac.size() == 0)
					return;
				actions.add(ac);
			}
			constraints.add(generateSingleConstraint(stateIndex, actions));
		}
	}
	
	private boolean crossReach(List<Integer> currStates, BitSet scc)
	{
		int size = currStates.size();
		for(int state : currStates)
		{
			boolean[] reach = new boolean[size];
			Stack<Integer> todo = new Stack<Integer>();
			todo.push(state);
			while(!todo.isEmpty())
			{
				int s = todo.pop();
				int numSucc = graph.getNumSuccessors(s);
				for(int succIter=0;succIter<numSucc;succIter++)
				{
					int succNode = graph.getSuccessorNode(s, succIter);
					if(!scc.get(succNode))
						continue;
					
					int numRealSucc = graph.getNumSuccessors(succNode);
					boolean isIn = true;
					for(int realSuccIter=0;realSuccIter<numRealSucc;realSuccIter++)
					{
						int realSucc = graph.getSuccessorNode(succNode, realSuccIter);
						if(!currStates.contains(realSucc))
						{
							isIn = false;
							break;
						}
					}
					if(isIn)
					{
						for(int realSuccIter=0;realSuccIter<numRealSucc;realSuccIter++)
						{
							int realSucc = graph.getSuccessorNode(succNode, realSuccIter);
							int index = currStates.indexOf(realSucc);
							if(!reach[index])
							{
								if(realSucc != state)
									todo.add(realSucc);
								reach[index] = true;
							}
						}
					}
				}
			}
			
			for(int i=0;i<size;i++)
			{
				if(!reach[i])
					return false;
			}
		}
		return true;
	}
	
	private String generateSingleConstraint(int[] stateIndex, List<List<String>> actions)
	{
		StringBuilder builder = new StringBuilder();
		List<Module> modules = ((ModelMAS) modelChecker.getModel()).getModelPrism().getModules();
        List<String> players = new ArrayList<String>();
        for(Module m : modules)
        {
        	players.add(m.getName());
        }
        int playerNum = players.size();
        builder.append("!(");
        for(int i = 0; i<stateIndex.length;i++)
        {
        	int state = stateIndex[i];
        	int acSize = actions.get(i).size();
        	builder.append("(");
        	for(int k=0;k<acSize;k++)
        	{
        		String globalAction = actions.get(i).get(k);
        		builder.append("(");
        		String[] localActions = globalAction.split(",");
        		for(int j=0;j<playerNum;j++)
            	{
            		String player = players.get(j);
            		BitSet bitSet = UtilPETL.getClassFor(player, state);
            		builder.append("p" + j + bitSet2String(bitSet) + localActions[j] + "=1");
            		if(j<playerNum-1)
            			builder.append("&");
            	}
        		builder.append(")");
        		if(k<acSize-1)
        			builder.append("|");
        	}
        	builder.append(")& !(x" + state + "=0)");
        	if(i<stateIndex.length-1)
    			builder.append("&");
        }
        builder.append(")");
    	
		return builder.toString();
	}
	
	private boolean checkSubset(BitSet scc, BitSet unKnown)
	{
		int numNodes = graph.getNumNodes();
		NodeProperty stateProp = graph.getNodeProperty(CommonProperties.STATE);
		for(int state = scc.nextSetBit(0);state>=0 && state<numNodes;state=scc.nextSetBit(state+1))
		{
			if(!stateProp.getBoolean(state))
				continue;
			if(!unKnown.get(state))
				return false;
		}
		return true;
	}
	
	private ConstraintSolver setBasicConstraints(BitSet unKnown, BitSet oneSet, BitSet zeroSet)
	{
		NodeProperty stateProp = graph.getNodeProperty(CommonProperties.STATE);
		
		ConstraintSolverConfiguration configuration = new ConstraintSolverConfiguration();
        configuration.requireFeature(Feature.SMT);
        ConstraintSolver solver = configuration.newProblem();
        TypeInteger typeInteger = TypeInteger.get();
        TypeReal typeReal = TypeReal.get();
        List<Module> modules = ((ModelMAS) modelChecker.getModel()).getModelPrism().getModules();
        List<String> players = new ArrayList<String>();
        for(Module m : modules)
        {
        	players.add(m.getName());
        }
        
        int nodeNum = graph.getNumNodes();
        for(int i=0;i<nodeNum;i++)
        {
        	if(stateProp.getBoolean(i))
        	{
        		solver.addVariable("x"+i, typeReal, newValue(typeReal, 0),newValue(typeReal, 1));
        	}
        }

        for(int state = oneSet.nextSetBit(0);state>=0 && state<nodeNum;state=oneSet.nextSetBit(state+1))
        {
        	solver.addConstraint(UtilPETL.parseExpression("x" + state + " = 1"));
        }
        for(int state = zeroSet.nextSetBit(0);state>=0 && state<nodeNum;state=zeroSet.nextSetBit(state+1))
        {
        	solver.addConstraint(UtilPETL.parseExpression("x" + state + " = 0"));
        }
        
        int playerNum = players.size();
        Map<String,Map<BitSet, List<String>>> playerSetToActions = new HashMap<String,Map<BitSet, List<String>>>();
        for(int playerIndex=0;playerIndex<playerNum;playerIndex++)
        {
        	String player = players.get(playerIndex);
        	List<BitSet> equivClasses = UtilPETL.getAllClassesOfPlayer(player, modelChecker);
        	Map<BitSet,List<String>> setToActions = new HashMap<BitSet,List<String>>();
        	int equivClassesNum = equivClasses.size();
        	for(int i=0;i<equivClassesNum;i++)
        	{
        		BitSet stateSet = equivClasses.get(i);
        		List<String> actions = new ArrayList<String>();
        		//there is at least one state, and all the states have the same actions set.
        		int state = stateSet.nextSetBit(0);

        		int numSucc = graph.getNumSuccessors(state);
        		StringBuilder builder = new StringBuilder();
        		for (int succNr = 0; succNr < numSucc; succNr++) {
                    EdgeProperty label = graph.getEdgeProperty(CommonProperties.TRANSITION_LABEL);
                    Value value = label.get(state, succNr);
                    Action ac = (Action) ((ValueObject)value).getObject();
                    String globalAction = ac.getName();
                    String localAction = globalAction.split(",")[playerIndex];
                    if(!actions.contains(localAction))
                    {
                    	if(succNr > 0)
	                    	builder.append("+");
                    	actions.add(localAction);
                    	if(!pIsReal)
                    		solver.addVariable("p" + playerIndex + bitSet2String(stateSet) + localAction, typeInteger, newValue(typeInteger, 0),newValue(typeInteger, 1));
                    	else
                    	{
                    		solver.addVariable("p" + playerIndex + bitSet2String(stateSet) + localAction, typeReal, newValue(typeReal, 0),newValue(typeReal, 1));
                    		solver.addConstraint(UtilPETL.parseExpression("p" + playerIndex + bitSet2String(stateSet) + localAction + "< 1 => p" + playerIndex + bitSet2String(stateSet) + localAction + "=0"));
                    		
                    	}
	                    builder.append("p" + playerIndex + bitSet2String(stateSet) + localAction);
                    }
                }
        		builder.append("=1");
        		//System.out.println(builder.toString() + "     " + state);
        		solver.addConstraint(UtilPETL.parseExpression(builder.toString()));
        		setToActions.put(stateSet, actions);
        	}
        	playerSetToActions.put(player, setToActions);
        }
  
        int help_variable_index = 0;
        for(int i=unKnown.nextSetBit(0);i>=0 && i<nodeNum;i=unKnown.nextSetBit(i+1))
        {
        	StringBuilder builder = new StringBuilder();
        	builder.append("x" + i + "=");
        	
        	List<List<String>> playerActions = new ArrayList<List<String>>();
        	Map<String, BitSet> playerToSet = new HashMap<String, BitSet>();
        	for(int j=0;j<playerNum;j++)
        	{
        		String player = players.get(j);
        		
        		BitSet bitSet = UtilPETL.getClassFor(player, i);
        		playerToSet.put(player, bitSet);
        		List<String> actions = playerSetToActions.get(player).get(bitSet);
        		playerActions.add(actions);
        	}
        	
        	List<List<String>> allPossibleActions = new ArrayList<List<String>>();
        	List<String> temp = new ArrayList<String>();
        	getAllPossibleActions(allPossibleActions,temp,playerActions);
        	int allActionNum = allPossibleActions.size();
        	for(int j=0;j<allActionNum;j++)
        	{
        		List<String> globalAction = allPossibleActions.get(j);
        		StringBuilder globalActionBuilder = new StringBuilder();
				String firstVar = "";
        		for(int k=0;k<playerNum;k++)
        		{
        			String localAction = globalAction.get(k);
        			String player = players.get(k);
        			globalActionBuilder.append(localAction);
        			if(k<playerNum-1)
        				globalActionBuilder.append(",");
        			if(!convert2Quadratic)
        			{
        				builder.append("p" + k + bitSet2String(playerToSet.get(player)) + localAction + "*");
        			}
        			else
        			{
        				if(k>0)
        				{
        					solver.addVariable("help_" + help_variable_index, typeInteger, newValue(typeInteger, 0),newValue(typeInteger, 1));
        					if(k>1)
        					{
        						int preHelpVar = help_variable_index - 1;
        						solver.addConstraint(UtilPETL.parseExpression("help_" + help_variable_index + "= help_" + preHelpVar 
        								+ "*" + "p" + k + bitSet2String(playerToSet.get(player)) + localAction));
        					}
        					else
        					{
        						solver.addConstraint(UtilPETL.parseExpression("help_" + help_variable_index + "=" + firstVar
        								+ "*" + "p" + k + bitSet2String(playerToSet.get(player)) + localAction));
        					}
        					help_variable_index++;
        				}
        				else
        				{
        					firstVar = "p" + k + bitSet2String(playerToSet.get(player)) + localAction;
        				}        				
        			}
        		}
        		if(convert2Quadratic)
        		{
        			int preHelpVar = help_variable_index - 1;
            		builder.append("help_" + preHelpVar + "*");
        		}
        		
        		String globalActionString = globalActionBuilder.toString();
        		builder.append("(");
        		int numSucc = graph.getNumSuccessors(i);
        		for (int succNr = 0; succNr < numSucc; succNr++) {
                    EdgeProperty label = graph.getEdgeProperty(CommonProperties.TRANSITION_LABEL);
                    Value value = label.get(i, succNr);
                    Action ac = (Action) ((ValueObject)value).getObject();
                    if(!ac.getName().equals(globalActionString))
                    	continue;
                    
                    int succ = graph.getSuccessorNode(i, succNr);
                    assert !stateProp.getBoolean(succ);
                    
                    int num_Succ = graph.getNumSuccessors(succ);
                    for(int nr=0;nr<num_Succ;nr++)
                    {
                    	EdgeProperty weight = graph.getEdgeProperty(CommonProperties.WEIGHT);
                        Value pro = weight.get(succ, nr);
                        int succState = graph.getSuccessorNode(succ, nr);
                        //builder.append(((ValueReal) pro).getDouble() + "*x" + succState);
                        builder.append( pro + "*x" + succState);
                        if(nr<num_Succ-1)
                        	builder.append("+");
                    }
                    //there is exactly one globalAction action
                    break;
                }
        		builder.append(")");
        		if(j<allPossibleActions.size()-1)
        			builder.append("+");
        	}
        	//System.out.println(builder.toString());
        	solver.addConstraint(UtilPETL.parseExpression(builder.toString()));
        }
        
        return solver;
	}
	
	private void getAllPossibleActions(List<List<String>> res, List<String> temp, List<List<String>> playerActions)
	{
		int size = temp.size();
		if(size == playerActions.size())
		{
			res.add(temp);
			return;
		}
		List<String> next = playerActions.get(size);
		for(String action : next)
		{
			List<String> newTemp = new ArrayList<String>(temp);
			newTemp.add(action);
			getAllPossibleActions(res,newTemp,playerActions);
		}
	}
	
	private BitSet computeUnKnownStates(BitSet oneSet, BitSet zeroSet)
	{
		BitSet unKnown = UtilBitSet.newBitSetUnbounded();
		int nodeNum = graph.getNumNodes();
		
		NodeProperty stateProp = graph.getNodeProperty(CommonProperties.STATE);
        for(int i=0;i<nodeNum;i++)
        {
        	if (!stateProp.getBoolean(i) || oneSet.get(i) || zeroSet.get(i)) {
                continue;
            }
        	unKnown.set(i);
        }
        
        BitSet canReach = UtilBitSet.newBitSetUnbounded();
        for(int i=unKnown.nextSetBit(0);i>=0 && i<nodeNum;i=unKnown.nextSetBit(i+1))
        {
        	Stack<Integer> stack = new Stack<Integer>();
        	stack.push(i);
        	BitSet visited = UtilBitSet.newBitSetUnbounded();
        	visited.set(i);
        	boolean reach =false;
        	while(!stack.isEmpty())
        	{
        		int state = stack.pop();
        		int numSucc = graph.getNumSuccessors(state);
        		boolean found = false;
        		for (int succNr = 0; succNr < numSucc; succNr++)
        		{
        			int succ = graph.getSuccessorNode(state, succNr);
        			assert !stateProp.getBoolean(succ);
                    
                    int num_Succ = graph.getNumSuccessors(succ);
                    boolean hasFound = false;
                    for(int nr=0;nr<num_Succ;nr++)
                    {
                    	int succState = graph.getSuccessorNode(succ, nr);
                    	if(oneSet.get(succState))
                    	{
                    		canReach.set(i);
                    		hasFound = true;
                    		break;
                    	}
                    	else if(canReach.get(succState))
                    	{
                    		hasFound = true;
                    		break;
                    	}
                    	else
                    	{
                    		if(!visited.get(succState))
                    		{
                    			visited.set(succState);
                    			if(!zeroSet.get(succState))
                    				stack.push(succState);
                    		}
                    	}
                    }
                    if(hasFound)
                    {
                    	found = true;
                    	break;
                    }
        		}
        		if(found)
        		{
        			reach = true;
        			break;
        		}
        	}
        	if(!reach)
        	{
        		for(int k= visited.nextSetBit(0);k>=0 && k<nodeNum;k=visited.nextSetBit(k+1))
            	{
            		zeroSet.set(k);
            		unKnown.clear(k);
            	}
        	}
        }
        return unKnown;
	}

	private int variableCounter = 0;
	private Map<String, String> variables = new HashMap<String, String>();
	private String bitSet2String(BitSet set)
	{
		assert(set != null && set.cardinality() != 0);
		
		int nodeNum = graph.getNumNodes();
		StringBuilder builder = new StringBuilder();
		for(int i=set.nextSetBit(0);i>=0 && i<nodeNum;i=set.nextSetBit(i+1))
		{
			builder.append("_" + i);
		}
		builder.append("_");
		
		String res = variables.get(builder.toString());
		if(res!=null)
			return res;
		res = "_" + variableCounter + "";
		variableCounter++;
		variables.put(builder.toString(), res);
		return res;
		//return builder.toString();
	}
	
	private int computeNumberOfEdges()
    {
    	int result = 0;
    	int nodeNum = graph.getNumNodes();
    	NodeProperty stateProp = graph.getNodeProperty(CommonProperties.STATE);
    	for(int node=0;node<nodeNum;node++)
    	{
    		if(!stateProp.getBoolean(node))
    			continue;
    		
    		int numSucc = graph.getNumSuccessors(node);
    		result += numSucc;
    		for (int succNr = 0; succNr < numSucc; succNr++)
    		{
    			int succ = graph.getSuccessorNode(node, succNr);
    			int num_Succ = graph.getNumSuccessors(succ);
    			result += num_Succ;
    		}
    	}
    	 	
    	return result;
    }
	
	@Override
	public Set<Object> getRequiredGraphProperties() {
		Set<Object> required = new LinkedHashSet<>();
        required.add(CommonProperties.SEMANTICS);
        return required;
	}

	@Override
	public Set<Object> getRequiredNodeProperties() {
		Set<Object> required = new LinkedHashSet<>();
        required.add(CommonProperties.STATE);
        required.add(CommonProperties.PLAYER);
        ExpressionQuantifier propertyQuantifier = (ExpressionQuantifier) property;
        Set<Expression> inners = UtilPETL.collectPCTLInner(propertyQuantifier.getQuantified());
        StateSet allStates = UtilGraph.computeAllStatesExplicit(modelChecker.getLowLevel());
        for (Expression inner : inners) {
            required.addAll(modelChecker.getRequiredNodeProperties(inner, allStates));
        }

        Set<Expression> expOfEquiv = ((ModelMAS) modelChecker.getModel()).getEquivalenceRelations().getAllExpressions();
        for (Expression inner : expOfEquiv) {
            required.addAll(modelChecker.getRequiredNodeProperties(inner, allStates));
        }
        
        return required;
	}

	@Override
	public Set<Object> getRequiredEdgeProperties() {
		Set<Object> required = new LinkedHashSet<>();
        required.add(CommonProperties.WEIGHT);
        required.add(CommonProperties.TRANSITION_LABEL);
        return required;
	}

	@Override
	public String getIdentifier() {
		return IDENTIFIER;
	}

	@Override
	public void setModelChecker(ModelChecker modelChecker) {
		assert modelChecker != null;
        this.modelChecker = modelChecker;
        if (modelChecker.getEngine() instanceof EngineExplicit) {
            this.graph = modelChecker.getLowLevel();
        }
	}

	@Override
	public void setProperty(Expression property) {
		this.property = property;
	}

	@Override
	public void setForStates(StateSet forStates) {
		this.forStates = forStates;
		
	}

	private void handleSimplePCTLExtensions() {
		ExpressionQuantifier propertyQuantifier = ExpressionQuantifier.as(property);
        Expression quantified = propertyQuantifier.getQuantified();
        if (isNot(quantified)
                && isFinally((ExpressionOperator.as(quantified)).getOperand1())) {
            ExpressionOperator quantifiedOperator = (ExpressionOperator) quantified;
            ExpressionTemporalFinally quantifiedOp1 =
                    ExpressionTemporalFinally.as(quantifiedOperator.getOperand1());
            quantified = new ExpressionTemporalGlobally.Builder()
                    .setOperand(new ExpressionOperator.Builder()
                            .setOperator(OperatorNot.NOT)
                            .setOperands(quantifiedOp1.getOperand())
                            .build())
                    .setTimeBound(quantifiedOp1.getTimeBound())
                    .setPositional(quantified.getPositional())
                    .build();
            property = new ExpressionQuantifier.Builder()
                    .setCmpType(propertyQuantifier.getCompareType())
                    .setCompare(propertyQuantifier.getCompare())
                    .setCondition(propertyQuantifier.getCondition())
                    .setDirType(propertyQuantifier.getDirType())
                    .setPositional(propertyQuantifier.getPositional())
                    .setQuantified(quantified)
                    .build();
        }
    }
	
	private static boolean isNot(Expression expression) {
        if (!(expression instanceof ExpressionOperator)) {
            return false;
        }
        ExpressionOperator expressionOperator = (ExpressionOperator) expression;
        return expressionOperator.getOperator()
                .equals(OperatorNot.NOT);
    }

	private static boolean isFinally(Expression expression) {
        return ExpressionTemporalFinally.is(expression);
    }

    private static boolean isGlobally(Expression expression) {
        return ExpressionTemporalGlobally.is(expression);
    }

    private static boolean isRelease(Expression expression) {
        return ExpressionTemporalRelease.is(expression);
    }
    
    private Expression not(Expression expression) {
        return new ExpressionOperator.Builder()
                .setOperator(OperatorNot.NOT)
                .setPositional(expression.getPositional())
                .setOperands(expression)
                .build();
    }
    
    private ValueArray newValueArrayWeight(int size) {
        TypeArray typeArray = TypeWeight.get().getTypeArray();
        return UtilValue.newArray(typeArray, size);
    }
    
    private StateMap solveDTMC(ExpressionTemporalUntil pathTemporal, boolean min, boolean negate, StateMapExplicit innerLeft, StateMapExplicit innerRight) {
    	//just the standard PCTL model checking. If there are bugs, please check the code of the latest version of EPMC
    	
    	assert pathTemporal != null;
        Semantics semanticsType = ValueObject.as(graph.getGraphProperty(CommonProperties.SEMANTICS)).getObject();
        TimeBound timeBound = pathTemporal.getTimeBound();

        BitSet sinkSet = UtilBitSet.newBitSetUnbounded();
        TypeAlgebra typeWeight = TypeWeight.get();
        Value zero = UtilValue.newValue(typeWeight, 0);
        Value one = UtilValue.newValue(typeWeight, 1);
        ValueArray resultValues = newValueArrayWeight(computeForStates.size());
        //        ValueArray result = typeArray.newValue(computeForStates.length());

        BitSet allNodes = UtilBitSet.newBitSetUnbounded();
        allNodes.set(0, graph.getNumNodes(), true);
        GraphSolverConfigurationExplicit configuration = UtilGraphSolver.newGraphSolverConfigurationExplicit();
        ValueAlgebra transValue = typeWeight.newValue();
        OperatorEvaluator set = ContextValue.get().getEvaluator(OperatorSet.SET, typeWeight, typeWeight);
        set.apply(transValue, UtilValue.newValue(typeWeight, 0));

        BitSet zeroSet = UtilBitSet.newBitSetUnbounded();
        BitSet oneSet = UtilBitSet.newBitSetUnbounded();
        NodeProperty stateProp = graph.getNodeProperty(CommonProperties.STATE);
        ValueBoolean valueLeft = TypeBoolean.get().newValue();
        ValueBoolean valueRight = TypeBoolean.get().newValue();
        for (int i = 0; i < innerLeft.size(); i++) {
            int state = innerLeft.getExplicitIthState(i);
            if (!stateProp.getBoolean(state)) {
                continue;
            }
            innerLeft.getExplicitIthValue(valueLeft, i);
            innerRight.getExplicitIthValue(valueRight, i);
            boolean left = valueLeft.getBoolean();
            boolean right = valueRight.getBoolean();
            if (!left && !right) {
                zeroSet.set(state);
            } else if (right) {
                oneSet.set(state);
            }
        }

        ValueArrayAlgebra values;
        NodeProperty isState = graph.getNodeProperty(CommonProperties.STATE);            
        if (timeBound.isRightBounded()) {
            if (SemanticsContinuousTime.isContinuousTime(semanticsType)) {
                GraphSolverObjectiveExplicitBoundedReachability objective = new GraphSolverObjectiveExplicitBoundedReachability();
                objective.setGraph(graph);
                objective.setMin(min);
                objective.setTime(ValueAlgebra.as(UtilEvaluatorExplicit.evaluate(timeBound.getRight())));
                objective.setZeroSink(zeroSet);
                objective.setTargets(oneSet);
                configuration.setObjective(objective);
                configuration.solve();
                values = objective.getResult();
            } else {
                int leftBound = ValueInteger.as(UtilEvaluatorExplicit.evaluate(timeBound.getLeft())).getInt();
                int rightBound = ValueInteger.as(UtilEvaluatorExplicit.evaluate(timeBound.getRight())).getInt();
                if (timeBound.isRightOpen()) {
                    rightBound--;
                }
                if (timeBound.isLeftOpen()) {
                    leftBound++;
                }
                GraphSolverObjectiveExplicitBoundedReachability objective = new GraphSolverObjectiveExplicitBoundedReachability();
                objective.setZeroSink(zeroSet);
                objective.setTargets(oneSet);
                objective.setMin(min);
                objective.setGraph(graph);
                Value time = UtilValue.newValue(TypeInteger.get(), rightBound - leftBound);
                objective.setTime(time);
                configuration.setObjective(objective);
                configuration.solve();
                values = objective.getResult();
            }
        } else {
            GraphSolverObjectiveExplicitUnboundedReachability objective = new GraphSolverObjectiveExplicitUnboundedReachability();
            objective.setTarget(oneSet);
            objective.setZeroSink(zeroSet);
            objective.setMin(min);
            objective.setGraph(graph);
            objective.setComputeFor(computeForStates.getStatesExplicit());
            //                System.out.println(graph);
            //              System.out.println(oneSet);
            configuration.setObjective(objective);
            configuration.solve();
            values = objective.getResult();
        }
        ValueBoolean cmp = TypeBoolean.get().newValue();
        OperatorEvaluator gt = ContextValue.get().getEvaluator(OperatorGt.GT, ValueAlgebra.as(UtilEvaluatorExplicit.evaluate(timeBound.getLeft())).getType(), ValueAlgebra.as(UtilEvaluatorExplicit.evaluate(timeBound.getLeft())).getType());
        gt.apply(cmp, ValueAlgebra.as(UtilEvaluatorExplicit.evaluate(timeBound.getLeft())), UtilValue.newValue(ValueAlgebra.as(UtilEvaluatorExplicit.evaluate(timeBound.getLeft())).getType(), 0));
        if (cmp.getBoolean() || timeBound.isLeftOpen()) {
            configuration = UtilGraphSolver.newGraphSolverConfigurationExplicit();
            sinkSet.clear();
            for (int i = 0; i < innerLeft.size(); i++) {
                int state = innerLeft.getExplicitIthState(i);
                if (isState.getBoolean(state)) {
                    innerLeft.getExplicitIthValue(valueLeft, i);
                    boolean left = valueLeft.getBoolean();
                    if (!left) {
                        sinkSet.set(state);
                        values.set(zero, state);
                    }
                }
            }
            Value val = typeWeight.newValue();

            for (int i = 0; i < computeForStates.size(); i++) {
                int state = computeForStates.getExplicitIthState(i);
                values.get(val, state);
                resultValues.set(val, i);
            }

            if (SemanticsContinuousTime.isContinuousTime(semanticsType)) {
                GraphSolverObjectiveExplicitBounded objective = new GraphSolverObjectiveExplicitBounded();
                configuration.setObjective(objective);
                objective.setGraph(graph);
                objective.setValues(values);
                objective.setMin(min);
                objective.setTime(ValueAlgebra.as(UtilEvaluatorExplicit.evaluate(timeBound.getLeft())));
                configuration.solve();
                values = objective.getResult();
            } else {
                int leftBound = ValueInteger.as(UtilEvaluatorExplicit.evaluate(timeBound.getLeft())).getInt();
                if (timeBound.isLeftOpen()) {
                    leftBound++;
                }
                GraphSolverObjectiveExplicitBounded objective = new GraphSolverObjectiveExplicitBounded();
                objective.setGraph(graph);
                objective.setValues(values);
                objective.setMin(min);
                objective.setComputeFor(computeForStates.getStatesExplicit());
                Value time = UtilValue.newValue(TypeInteger.get(), leftBound);
                objective.setTime(time);
                configuration.setObjective(objective);
                configuration.solve();
                values = objective.getResult();
            }
        }
        Value val = typeWeight.newValue();
        for (int i = 0; i < computeForStates.size(); i++) {
            int state = computeForStates.getExplicitIthState(i);
            values.get(val, i);
            resultValues.set(val, i);
        }
        OperatorEvaluator subtract = ContextValue.get().getEvaluator(OperatorSubtract.SUBTRACT, typeWeight, typeWeight);
        if (negate) {
            ValueAlgebra entry = typeWeight.newValue();            
            for (int i = 0; i < resultValues.size(); i++) {
                resultValues.get(entry, i);
                subtract.apply(entry, one, entry);
                resultValues.set(entry, i);
            }
        }
        return UtilGraph.newStateMap(computeForStates.clone(), resultValues);
    }

}
