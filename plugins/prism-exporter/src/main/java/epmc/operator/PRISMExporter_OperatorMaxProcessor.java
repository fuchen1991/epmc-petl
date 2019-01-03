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

import epmc.expression.standard.ExpressionOperator;
import epmc.prism.exporter.operatorprocessor.PRISMExporter_OperatorProcessorStrict;
import epmc.prism.exporter.processor.PRISMExporter_ProcessorRegistrar;

/**
 * @author Andrea Turrini
 *
 */
public class PRISMExporter_OperatorMaxProcessor implements PRISMExporter_OperatorProcessorStrict {

    private ExpressionOperator expressionOperator = null;
    
    /* (non-Javadoc)
     * @see epmc.prism.exporter.processor.JANI2PRISMOperatorProcessorStrict#setExpressionOperator(epmc.expression.standard.ExpressionOperator)
     */
    @Override
    public PRISMExporter_OperatorProcessorStrict setExpressionOperator(ExpressionOperator expressionOperator) {
        assert expressionOperator != null;
        
        assert expressionOperator.getOperator().equals(OperatorMax.MAX);
    
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

        prism.append("max(")
            .append(PRISMExporter_ProcessorRegistrar.getProcessor(expressionOperator.getOperand1())
                    .toPRISM())
            .append(", ")
            .append(PRISMExporter_ProcessorRegistrar.getProcessor(expressionOperator.getOperand2())
                        .toPRISM())
            .append(")");

        return prism.toString();
    }
}
