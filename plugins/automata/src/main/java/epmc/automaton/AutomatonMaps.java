package epmc.automaton;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import epmc.expression.Expression;
import epmc.value.Value;
import epmc.value.ValueBoolean;

// TODO complete documentation

/**
 * Class to support the implementation of automata.
 * <p>
 * Classes implementing the {@link Automaton} interface may use this class as a
 * convenient means to implement tasks such as mapping state and label objects
 * to numbers, to cache successors and so forth.
 * </p>
 * <p>
 * Having this functionality in a separate task rather than making
 * {@link Automaton} an abstract class which already implements these tasks
 * increases flexibility, because classes which do not need (or only need part
 * of) the functionality provided by this class may simply not use it, and
 * provide their own implementation instead. Also, the fact that
 * {@link Automaton} is an interface and not an abstract class means that
 * automata can inherit from arbitrary other classes, if useful.
 * </p>
 * 
 * @author Ernst Moritz Hahn
 */
public final class AutomatonMaps {
    private final Map<AutomatonStateUtil,AutomatonStateUtil> states = new HashMap<>();
    private final List<AutomatonStateUtil> numberToState = new ArrayList<>();
    private final List<AutomatonLabelUtil> numberToLabel = new ArrayList<>();
    private final Map<AutomatonLabelUtil,AutomatonLabelUtil> labels = new HashMap<>();
    private int[] successors;
    private int successorsPerEntry;
    
    public int getNumStates() {
        return states.size();
    }
    
    public <T extends AutomatonStateUtil> T makeUnique(T state) {
        assert state != null;
        @SuppressWarnings("unchecked")
        T result = (T) states.get(state);
        if (result == null) {
            state.setNumber(states.size());
            states.put(state,state);
            result = state;
            numberToState.add(state);
        }
        return result;
    }
    
    public <T extends AutomatonLabelUtil> T makeUnique(T label) {
        assert label != null;
        @SuppressWarnings("unchecked")
        T result = (T) labels.get(label);
        if (result == null) {
            label.setNumber(labels.size());
            labels.put(label,label);
            result = label;
            numberToLabel.add(label);
        }
        return result;
    }

    public AutomatonStateUtil numberToState(int number) {
        assert number >= 0;
        return numberToState.get(number);
    }

    public AutomatonLabelUtil numberToLabel(int number) {
        assert number >= 0;
        return numberToLabel.get(number);
    }
    
    public void initialiseCache(Expression[] expressions) {
        assert expressions != null;
        successorsPerEntry = 1;
        for (Expression expression : expressions) {
            assert expression != null;
        }
        for (int i = 0; i < expressions.length; i++) {
        	//                assert TypeBoolean.isBoolean(expressions[i].getType());
        	successorsPerEntry *= 2;
        }
        this.successors = new int[1];
        this.successors[0] = -1;
    }

    public void insertSuccessorEntry(Value[] modelState, int automatonState,
            int successorState, int successorLabel) {
        int index = successorsPerEntry * automatonState;
        int indexAdd = 0;
        int bit = 1;
        for (int i = 0; i < modelState.length; i++) {
            indexAdd |= ValueBoolean.asBoolean(modelState[i]).getBoolean() ? bit : 0;
            bit <<= 1;
        }
        index += indexAdd;
        ensureSuccessorsLength(index * 2 + 2);
        successors[index * 2] = successorState;
        successors[index * 2 + 1] = successorLabel;
    }
    
    public long lookupSuccessorEntry(Value[] modelState, int automatonState) {
        int index = successorsPerEntry * automatonState;
        int indexAdd = 0;
        int bit = 1;
        for (int i = 0; i < modelState.length; i++) {
            indexAdd |= ValueBoolean.asBoolean(modelState[i]).getBoolean() ? bit : 0;
            bit <<= 1;
        }
        index += indexAdd;
        ensureSuccessorsLength(index * 2 + 2);
        if (successors[index * 2 + 1] == -1) {
            return -1;
        }
        int successorState = successors[index * 2];
        int successorLabel = successors[index * 2 + 1];
        long both = (((long) successorState) << 32) | (successorLabel);
        return both;
    }
    
    public static int getSuccessorState(long combined) {
        return (int) (combined >>>= 32);
    }
    
    public static int getSuccessorLabel(long combined) {
        return (int) (combined & 0xFFFFL);
    }

    private void ensureSuccessorsLength(int requiredLength) {
        assert requiredLength >= 0;
        if (successors.length >= requiredLength) {
            return;
        }
        int newLength = successors.length;
        while (newLength < requiredLength) {
            newLength *= 2;
        }
        int[] newSuccessors = new int[newLength];
        System.arraycopy(successors, 0, newSuccessors, 0, successors.length);
        Arrays.fill(newSuccessors, successors.length, newLength, -1);
        successors = newSuccessors;
        assert successors.length >= requiredLength;
    }
}
