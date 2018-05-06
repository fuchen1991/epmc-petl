/****************************************************************************

    ePMC - an extensible probabilistic model checker
    Copyright (C) 2017

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.

 *****************************************************************************/

package epmc.propertysolver;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import epmc.expression.Expression;
import epmc.expression.standard.ExpressionOperator;
import epmc.expression.standard.ExpressionPropositional;
import epmc.expression.standard.ExpressionQuantifier;
import epmc.expression.standard.ExpressionTemporalFinally;
import epmc.expression.standard.ExpressionTemporalGlobally;
import epmc.expression.standard.ExpressionTemporalNext;
import epmc.expression.standard.ExpressionTemporalRelease;
import epmc.expression.standard.ExpressionTemporalUntil;
import epmc.modelchecker.ModelChecker;
import epmc.petl.model.EquivalenceClasses;
import epmc.petl.model.ExpressionKnowledge;
import epmc.petl.model.KnowledgeType;
import epmc.prism.model.PropertyPRISM;
import epmc.util.BitSet;

/**
 * Utility class for PETL model checking
 * 
 * @author Chen Fu
 */

public class UtilPETL {
	private static EquivalenceClasses equivalenceClasses;
	
	public static Set<Expression> collectPETLInner(Expression expression) {
		if (ExpressionTemporalNext.is(expression)) {
            ExpressionTemporalNext expressionTemporal = ExpressionTemporalNext.as(expression);
            return collectPCTLInner(expressionTemporal.getOperand());
        } else if (ExpressionTemporalFinally.is(expression)) {
            ExpressionTemporalFinally expressionTemporal = ExpressionTemporalFinally.as(expression);
            return collectPCTLInner(expressionTemporal.getOperand());
        } else if (ExpressionTemporalGlobally.is(expression)) {
            ExpressionTemporalGlobally expressionTemporal = ExpressionTemporalGlobally.as(expression);
            return collectPCTLInner(expressionTemporal.getOperand());
        } else if (ExpressionTemporalRelease.is(expression)) {
            ExpressionTemporalRelease expressionTemporal = ExpressionTemporalRelease.as(expression);
            Set<Expression> result = new LinkedHashSet<>();
            result.addAll(collectPCTLInner(expressionTemporal.getOperandLeft()));
            result.addAll(collectPCTLInner(expressionTemporal.getOperandRight()));
            return result;
        } else if (ExpressionTemporalUntil.is(expression)) {
            ExpressionTemporalUntil expressionTemporal = ExpressionTemporalUntil.as(expression);
            Set<Expression> result = new LinkedHashSet<>();
            result.addAll(collectPCTLInner(expressionTemporal.getOperandLeft()));
            result.addAll(collectPCTLInner(expressionTemporal.getOperandRight()));
            return result;
        } else {
            return Collections.singleton(expression);
        }
    }
	
	public static List<BitSet> getAllClassesOfPlayer(String player, ModelChecker modelChecker)
	{
		if(equivalenceClasses == null || !equivalenceClasses.isInitalized())
		{
			equivalenceClasses = new EquivalenceClasses(modelChecker);
		}
		
		return equivalenceClasses.getClassesOfPlayer(player);
	}
	
	public static BitSet getClassFor(String player, int state)
	{
		assert equivalenceClasses != null;
		
		return equivalenceClasses.getClassFor(player,state);
	}
	
	public static BitSet getEquivalenceClass(int state, Expression expression, ModelChecker modelChecker)
	{
		assert expression instanceof ExpressionKnowledge;
		
		if(equivalenceClasses == null || !equivalenceClasses.isInitalized())
		{
			equivalenceClasses = new EquivalenceClasses(modelChecker);
		}
		ExpressionKnowledge exp = (ExpressionKnowledge) expression;
		KnowledgeType type = exp.getType();
		if(type == KnowledgeType.K)
		{
			assert exp.getPlayers().size() == 1;
			return equivalenceClasses.getClassFor(exp.getPlayers().get(0), state);
		}
		else
		{
			if(type == KnowledgeType.E)
			{
				return computeEveryoneKnowledge(exp.getPlayers(),state);
			}
			else if(type == KnowledgeType.C)
			{
				int size = 1;
				BitSet res = computeEveryoneKnowledge(exp.getPlayers(),state);
				while(size != res.cardinality())
				{
					size = res.cardinality();
					for(int i=res.nextSetBit(0);i>=0;i=res.nextSetBit(i+1))
					{
						res.or(computeEveryoneKnowledge(exp.getPlayers(),i));
					}
				}

				return res;
			}
			else if(type == KnowledgeType.D)
			{
				BitSet res = null;
				for(String player : exp.getPlayers())
				{
					BitSet tmp = equivalenceClasses.getClassFor(player,state);
					if(res == null)
						res = tmp;
					else
						res.and(tmp);
				}
				return res;
			}
		}
		
		return null;
	}
	
	private static BitSet computeEveryoneKnowledge(List<String> players, int state)
	{
		BitSet res = null;
		for(String player : players)
		{
			BitSet tmp = equivalenceClasses.getClassFor(player,state);
			if(res == null)
				res = tmp;
			else
				res.or(tmp);
		}
		return res;
	}
	
	public static boolean isSubsetOf(BitSet op1, BitSet op2)
	{
		assert op1 != null;
		assert op2 != null;
		
		for(int i= op1.nextSetBit(0);i>=0;i=op1.nextSetBit(i+1))
		{
			if(!op2.get(i))
				return false;
		}
		return true;
	}
	
	public static boolean isPCTLPath(Expression pathProp)
	{
		if (ExpressionTemporalNext.is(pathProp)) {
            ExpressionTemporalNext next = ExpressionTemporalNext.as(pathProp);
            return isPCTLState(next.getOperand());
        } else if (ExpressionTemporalFinally.is(pathProp)) {
            ExpressionTemporalFinally expFinally = ExpressionTemporalFinally.as(pathProp);
            return isPCTLState(expFinally.getOperand());
        } else if (ExpressionTemporalGlobally.is(pathProp)) {
            ExpressionTemporalGlobally expGlobally = ExpressionTemporalGlobally.as(pathProp);
            return isPCTLState(expGlobally.getOperand());
        } else if (ExpressionTemporalRelease.is(pathProp)) {
            ExpressionTemporalRelease expRelease = ExpressionTemporalRelease.as(pathProp);
            return isPCTLState(expRelease.getOperandLeft())
                    && isPCTLState(expRelease.getOperandRight());
        } else if (ExpressionTemporalUntil.is(pathProp)) {
            ExpressionTemporalUntil expRelease = ExpressionTemporalUntil.as(pathProp);
            return isPCTLState(expRelease.getOperandLeft())
                    && isPCTLState(expRelease.getOperandRight());
        } else {
            return false;
        }
	}
	
	public static boolean isPCTLState(Expression stateProp)
	{
		if (!(stateProp instanceof ExpressionPropositional) && !(stateProp instanceof ExpressionKnowledge) && !(stateProp instanceof ExpressionQuantifier)) {
            return false;
        }
		
		if(stateProp instanceof ExpressionPropositional)
		{
			if(!(stateProp instanceof ExpressionOperator))
				return true;
			
			ExpressionOperator asOperator = (ExpressionOperator) stateProp;
			for(Expression operand : asOperator.getOperands())
			{
				if(!isPCTLState(operand))
					return false;
			}
		}
		if(stateProp instanceof ExpressionKnowledge)
		{
			ExpressionKnowledge asKnowledge = (ExpressionKnowledge) stateProp;
			if(!isPCTLState(asKnowledge.getQuantifier()))
				return false;
		}
		if(stateProp instanceof ExpressionQuantifier)
		{
			ExpressionQuantifier asQuantifier = (ExpressionQuantifier) stateProp;
			if(!isPCTLPath(asQuantifier.getQuantified()))
			{
				return false;
			}
		}
		
		return true;
	}
	
	public static Set<Expression> collectPCTLInner(Expression expression) {
		Set<Expression> result = new LinkedHashSet<>();
		if (ExpressionTemporalNext.is(expression)) {
            ExpressionTemporalNext next = ExpressionTemporalNext.as(expression);
            result.addAll(collectPCTLInner(next.getOperand()));
            return result;
        } else if (ExpressionTemporalFinally.is(expression)) {
            ExpressionTemporalFinally expFinally = ExpressionTemporalFinally.as(expression);
            result.addAll(collectPCTLInner(expFinally.getOperand()));
            return result;
        } else if (ExpressionTemporalGlobally.is(expression)) {
            ExpressionTemporalGlobally expGlobally = ExpressionTemporalGlobally.as(expression);
            result.addAll(collectPCTLInner(expGlobally.getOperand()));
            return result;
        } else if (ExpressionTemporalRelease.is(expression)) {
            ExpressionTemporalRelease expRelease = ExpressionTemporalRelease.as(expression);
            result.addAll(collectPCTLInner(expRelease.getOperandLeft()));
            result.addAll(collectPCTLInner(expRelease.getOperandRight()));
            return result;
        } else if (ExpressionTemporalUntil.is(expression)) {
            ExpressionTemporalUntil expRelease = ExpressionTemporalUntil.as(expression);
            result.addAll(collectPCTLInner(expRelease.getOperandLeft()));
            result.addAll(collectPCTLInner(expRelease.getOperandRight()));
            return result;
        } else if (expression instanceof ExpressionKnowledge) {
        	ExpressionKnowledge expressionKnowledge = (ExpressionKnowledge) expression;
            for (Expression inner : expressionKnowledge.getChildren()) {
                result.addAll(collectPCTLInner(inner));
            }
            return result;
        } else {
            return Collections.singleton(expression);			
        }
    }
	
	public static boolean isPCTLPathUntil(Expression pathProp) {
        if (!isPCTLPath(pathProp)) {
            return false;
        }
        if (ExpressionTemporalFinally.is(pathProp)) {
            return true;
        }
        if (ExpressionTemporalGlobally.is(pathProp)) {
            return true;
        }
        if (ExpressionTemporalRelease.is(pathProp)) {
            return true;
        }
        if (ExpressionTemporalUntil.is(pathProp)) {
            return true;
        }
        return false;
    }
	
	public static Expression parseExpression(String exp)
	{
		InputStream stream = new ByteArrayInputStream(exp.getBytes());
        return new PropertyPRISM().parseExpression(exp, stream);
	}
}
