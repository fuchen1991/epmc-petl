package epmc.expression.standard;

import static epmc.error.UtilError.ensure;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;

import epmc.value.OperatorNot;
import epmc.value.OperatorPow;
import epmc.value.OperatorSubtract;
import epmc.error.EPMCException;
import epmc.error.Positional;
import epmc.expression.Expression;
import epmc.expression.ExpressionToType;
import epmc.value.Operator;
import epmc.value.Type;
import epmc.value.OperatorAdd;
import epmc.value.OperatorAddInverse;
import epmc.value.OperatorCeil;
import epmc.value.OperatorDivide;
import epmc.value.OperatorFloor;
import epmc.value.OperatorIte;
import epmc.value.OperatorLog;
import epmc.value.OperatorMax;
import epmc.value.OperatorMin;
import epmc.value.OperatorMod;
import epmc.value.OperatorMultiply;

/**
 * Expression to store an operator.
 * 
 * @author Ernst Moritz Hahn
 */
public final class ExpressionOperator implements ExpressionPropositional {
    public final static class Builder {
        private Positional positional;
        private List<Expression> operands;
        private Operator operator;

        public Builder setPositional(Positional positional) {
            this.positional = positional;
            return this;
        }
        
        private Positional getPositional() {
            return positional;
        }
        
        public Builder setOperands(List<Expression> operands) {
            this.operands = operands;
            return this;
        }
        
        private List<Expression> getOperands() {
            return operands;
        }
        
        public Expression getOperand1() {
            return getOperands().get(0);
        }

        public Expression getOperand2() {
            return getOperands().get(1);
        }

        public Expression getOperand3() {
            return getOperands().get(2);
        }

        public Builder setOperands(Expression... operands) {
            this.operands = Arrays.asList(operands);
            return this;
        }
        
        public Builder setOperator(Operator operator) {
            this.operator = operator;
            return this;
        }
        
        private Operator getOperator() {
            return operator;
        }
        
        public ExpressionOperator build() {
            return new ExpressionOperator(this);
        }
    }

    public static boolean isOperator(Expression expression) {
    	return expression instanceof ExpressionOperator;
    }

    public static ExpressionOperator asOperator(Expression expression) {
    	if (isOperator(expression)) {
    		return (ExpressionOperator) expression;
    	} else {
    		return null;
    	}
    }
    
    private final Positional positional;
    private final List<Expression> operands = new ArrayList<>();
    private final Operator operator;

    private ExpressionOperator(Builder builder) {
        assert builder != null;
        assert builder.getOperator() != null;
        for (Expression child : builder.getOperands()) {
            assert child != null;
        }
        this.operands.addAll(builder.getOperands());
        if (builder.getOperator() != null) {
            this.operator = builder.getOperator();
        } else {
            throw new RuntimeException();
        }
        this.positional = builder.getPositional();
    }

    // public methods

    public List<Expression> getOperands() {
        return getChildren();
    }
    
    public Expression getOperand1() {
        return getOperands().get(0);
    }

    public Expression getOperand2() {
        return getOperands().get(1);
    }

    public Expression getOperand3() {
        return getOperands().get(2);
    }

    public Operator getOperator() {
        return operator;
    }    
    
    @Override
    public Expression replaceChildren(List<Expression> children) {
        return new ExpressionOperator.Builder()
                .setOperands(children)
                .setOperator(operator)
                .setPositional(positional)
                .build();
    }

    @Override
    public Type getType(ExpressionToType expressionToType) throws EPMCException {
    	assert expressionToType != null;
        Type result = expressionToType.getType(this);
        if (result != null) {
            return result;
        }
        
        List<Expression> operands = getOperands();
        Type[] opTypes = new Type[operands.size()];
        for (int opNr = 0; opNr < opTypes.length; opNr++) {
            Expression child = operands.get(opNr);
            Type childType = child.getType(expressionToType);
            assert childType != null : this + "    in    " + child + " " + child.getClass();
            opTypes[opNr] = childType;
        }
        result = this.operator.resultType(opTypes);
//        assert result != null : this + " ... " + this.getOperator().getIdentifier() + "  " + this.getClass() + " " + Arrays.toString(opTypes);
        ensure(result != null, ProblemsExpression.VALUE_INCONSISTENT_INFO);
        return result;
    }
    
    @Override
    public boolean isPropositional() {
        for (Expression operand : getOperands()) {
            if (!ExpressionPropositional.isPropositional(operand)) {
                return false;
            }
        }
        
        return true;
    }
    
    public boolean isAdd() {
        return operator.getIdentifier().equals(OperatorAdd.IDENTIFIER);
    }
    
    public boolean isSubtract() {
        return operator.getIdentifier().equals(OperatorSubtract.IDENTIFIER);
    }
    
    public boolean isMultiply() {
        return operator.getIdentifier().equals(OperatorMultiply.IDENTIFIER);
    }
    
    public boolean isDivide() {
        return operator.getIdentifier().equals(OperatorDivide.IDENTIFIER);
    }
    
    @Override
    public List<Expression> getChildren() {
        return operands;
    }

    @Override
    public Positional getPositional() {
        return positional;
    }
    
    
    @Override
    public final String toString() {
        StringBuilder builder = new StringBuilder();
        switch (operator.getIdentifier()) {
        case OperatorNot.IDENTIFIER:
        case OperatorAddInverse.IDENTIFIER:
            builder.append(operator);
            builder.append("(");
            builder.append(getOperand1());
            builder.append(")");
            break;
        case OperatorIte.IDENTIFIER:
            builder.append("(");
            builder.append(getOperand1());
            builder.append(")");
            builder.append(" ? ");
            builder.append("(");
            builder.append(getOperand2());
            builder.append(")");
            builder.append(" : ");
            builder.append("(");
            builder.append(getOperand3());
            builder.append(")");
            break;
        case OperatorMin.IDENTIFIER: case OperatorMax.IDENTIFIER: case OperatorPow.IDENTIFIER: case OperatorMod.IDENTIFIER: case OperatorLog.IDENTIFIER:
            builder.append(operator);
            builder.append("(");
            builder.append(getOperand1());
            builder.append(",");
            builder.append(getOperand2());
            builder.append(")");
            break;
        case OperatorFloor.IDENTIFIER: case OperatorCeil.IDENTIFIER:
            builder.append(operator);
            builder.append("(");
            builder.append(getOperand1());
            builder.append(")");
            break;
        default: {
            if (getChildren().size() == 1) {
                builder.append(operator);
                builder.append("(");
                builder.append(getChildren().get(0));
                builder.append(")");
            } else {
            Iterator<Expression> iter = getChildren().iterator();
            while (iter.hasNext()) {
                Expression child = iter.next();
                boolean needBraces = true;
                if (child instanceof ExpressionOperator) {
                    ExpressionOperator childOp = (ExpressionOperator) child;
                    if (operator == childOp.operator) {
                        needBraces = false;
                    }
                    if ((isAdd() || isSubtract())
                            && (childOp.isMultiply() || childOp.isDivide())) {
                        needBraces = false;
                    }
                }
                if (needBraces) {
                    builder.append("(");
                }
                builder.append(child);
                if (needBraces) {
                    builder.append(")");
                }
                if (iter.hasNext()) {
                    builder.append(" " + operator + " ");
                }
            }
            }
            break;
        }
        }
        if (getPositional() != null) {
            builder.append(" (" + getPositional() + ")");
        }
        return builder.toString();
    }

    @Override
    public boolean equals(Object obj) {
        assert obj != null;
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        ExpressionOperator other = (ExpressionOperator) obj;
        List<Expression> thisChildren = this.getChildren();
        List<Expression> otherChildren = other.getChildren();
        if (thisChildren.size() != otherChildren.size()) {
            return false;
        }
        for (int entry = 0; entry < thisChildren.size(); entry++) {
            if (!thisChildren.get(entry).equals(otherChildren.get(entry))) {
                return false;
            }
        }
        return this.operator == other.operator;
    }    
    
    @Override
    public int hashCode() {
        int hash = 0;
        hash = getClass().hashCode() + (hash << 6) + (hash << 16) - hash;
        for (Expression expression : this.getChildren()) {
            assert expression != null;
            hash = expression.hashCode() + (hash << 6) + (hash << 16) - hash;
        }
        hash = operator.hashCode() + (hash << 6) + (hash << 16) - hash;            
        return hash;
    }
}
