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

package epmc.jani.explorer;

import epmc.error.EPMCException;
import epmc.expression.Expression;
import epmc.expression.evaluatorexplicit.EvaluatorExplicit;
import epmc.expression.standard.UtilExpressionStandard;
import epmc.expression.standard.evaluatorexplicit.UtilEvaluatorExplicit;
import epmc.graph.explorer.Explorer;
import epmc.graph.explorer.ExplorerNodeProperty;
import epmc.value.Type;
import epmc.value.Value;

final class PropertyNodeExpression implements ExplorerNodeProperty {
	private final ExplorerJANI explorer;
	private final EvaluatorExplicit evaluator;
	private final Type type;
	private final Value[] values;

	PropertyNodeExpression(ExplorerJANI explorer, Expression[] identifiers, Expression expression, Type type) throws EPMCException {
		assert explorer != null;
		assert expression != null;
		expression = UtilExpressionStandard.replace(expression, explorer.getModel().getConstants());
		this.explorer = explorer;
		this.evaluator = UtilEvaluatorExplicit.newEvaluator(expression, explorer, identifiers);
		this.type = type;
		this.values = new Value[identifiers.length];
	}
	
	@Override
	public Explorer getExplorer() {
		return explorer;
	}

	@Override
	public Value get() throws EPMCException {
		evaluator.evaluate(values);
		return evaluator.getResultValue();
	}

	public void setVariableValues(Value[] values) {
		for (int valueNr = 0; valueNr < values.length; valueNr++) {
			this.values[valueNr] = values[valueNr];
		}
	}
	
	@Override
	public Type getType() {
		return type;
	}
}