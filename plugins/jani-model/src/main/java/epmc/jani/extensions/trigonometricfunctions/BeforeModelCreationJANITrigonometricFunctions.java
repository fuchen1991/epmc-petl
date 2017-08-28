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

package epmc.jani.extensions.trigonometricfunctions;

import epmc.plugin.BeforeModelCreation;
import epmc.value.ContextValue;

public final class BeforeModelCreationJANITrigonometricFunctions implements BeforeModelCreation {
    /** Identifier of this class. */
    public final static String IDENTIFIER = "before-model-loading-jani-trigonometric-functions";

    @Override
    public String getIdentifier() {
        return IDENTIFIER;
    }

    @Override
    public void process() {
        ContextValue.get().addOperatorEvaluator(OperatorEvaluatorSin.INSTANCE);
        ContextValue.get().addOperatorEvaluator(OperatorEvaluatorCos.INSTANCE);
        ContextValue.get().addOperatorEvaluator(OperatorEvaluatorTan.INSTANCE);
        ContextValue.get().addOperatorEvaluator(OperatorEvaluatorAsin.INSTANCE);
        ContextValue.get().addOperatorEvaluator(OperatorEvaluatorAcos.INSTANCE);
        ContextValue.get().addOperatorEvaluator(OperatorEvaluatorAtan.INSTANCE);
    }
}
