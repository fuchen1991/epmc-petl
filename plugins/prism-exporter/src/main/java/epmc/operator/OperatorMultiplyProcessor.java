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

package epmc.operator;

import static epmc.prism.exporter.util.UtilPRISMExporter.appendWithParenthesesIfNeeded;

import epmc.expression.Expression;
import epmc.expression.standard.ExpressionOperator;
import epmc.prism.exporter.operatorprocessor.JANI2PRISMOperatorProcessorStrict;

/**
 * @author Andrea Turrini
 *
 */
public class OperatorMultiplyProcessor implements JANI2PRISMOperatorProcessorStrict {

    private ExpressionOperator expressionOperator = null;
    
    /* (non-Javadoc)
     * @see epmc.prism.exporter.processor.JANI2PRISMOperatorProcessorStrict#setExpressionOperator(epmc.expression.standard.ExpressionOperator)
     */
    @Override
    public JANI2PRISMOperatorProcessorStrict setExpressionOperator(ExpressionOperator expressionOperator) {
        assert expressionOperator != null;
        
        assert expressionOperator.getOperator().equals(OperatorMultiply.MULTIPLY);
    
        this.expressionOperator = expressionOperator;
        return this;
    }

    /* (non-Javadoc)
     * @see epmc.prism.exporter.operatorprocessor.JANI2PRISMOperatorProcessorStrict#toPRISM()
     */
    @Override
    public String toPRISM() {
        assert expressionOperator != null;

        StringBuilder prism = new StringBuilder();

        appendWithParenthesesIfNeeded(this, expressionOperator.getOperand1(), prism);
        prism.append(" * ");
        appendWithParenthesesIfNeeded(this, expressionOperator.getOperand2(), prism);

        return prism.toString();
    }
    /* (non-Javadoc)
     * @see epmc.prism.exporter.operatorprocessor.JANI2PRISMOperatorProcessorStrict#needsParentheses(epmc.expression.standard.Expression)
     */
    @Override
    public boolean needsParentheses(Expression childOperand) {
        if (childOperand instanceof ExpressionOperator) {
            Operator operator = ((ExpressionOperator) childOperand).getOperator();
            if (operator.equals(OperatorMultiply.MULTIPLY))
                return false;
            if (operator.equals(OperatorMultiplyInverse.MULTIPLY_INVERSE))
                return false;
            if (operator.equals(OperatorDivide.DIVIDE))
                return false;
        }
        return JANI2PRISMOperatorProcessorStrict.super.needsParentheses(childOperand);
    }
}
