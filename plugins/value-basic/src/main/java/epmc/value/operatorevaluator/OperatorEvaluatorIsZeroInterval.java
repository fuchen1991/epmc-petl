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

package epmc.value.operatorevaluator;

import epmc.value.ContextValue;
import epmc.value.Operator;
import epmc.value.OperatorEvaluator;
import epmc.value.Type;
import epmc.value.TypeBoolean;
import epmc.value.TypeInterval;
import epmc.value.Value;
import epmc.value.ValueBoolean;
import epmc.value.ValueInterval;
import epmc.value.operator.OperatorIsZero;

public enum OperatorEvaluatorIsZeroInterval implements OperatorEvaluator {
    INSTANCE;

    @Override
    public Operator getOperator() {
        return OperatorIsZero.IS_ZERO;
    }

    @Override
    public boolean canApply(Type... types) {
        assert types != null;
        for (Type type : types) {
            assert type != null;
        }
        if (types.length != 1) {
            return false;
        }
        for (Type type : types) {
            if (!TypeInterval.is(type)) {
                return false;
            }
        }
        return true;
    }

    @Override
    public Type resultType(Type... types) {
        assert types != null;
        for (Type type : types) {
            assert type != null;
        }
        return TypeBoolean.get();
    }

    @Override
    public void apply(Value result, Value... operands) {
        assert result != null;
        assert operands != null;
        for (Value operand : operands) {
            assert operand != null;
        }
        ValueInterval operand = ValueInterval.as(operands[0]);
        OperatorEvaluator isZero = ContextValue.get().getEvaluator(OperatorIsZero.IS_ZERO, operand.getType().getEntryType());
        ValueBoolean cmp = TypeBoolean.get().newValue();
        isZero.apply(cmp, operand.getIntervalLower());
        if (!cmp.getBoolean()) {
            ValueBoolean.as(result).set(false);
            return;
        }
        isZero.apply(cmp, operand.getIntervalUpper());
        if (!cmp.getBoolean()) {
            ValueBoolean.as(result).set(false);
            return;
        }
        ValueBoolean.as(result).set(true);
    }
}
