package epmc.graph.explicit;

import epmc.error.EPMCException;
import epmc.value.Type;
import epmc.value.TypeInteger;
import epmc.value.Value;
import epmc.value.ValueInteger;

/**
 * Space-efficient implementation of a simple scheduler using Java arrays.
 * Similar to {@link SchedulerSimpleArray}, this scheduler stores its decisions
 * in a Java array. However, in contrast to {@link SchedulerSimpleArray},
 * decisions do not necessarily use a full integer to be stored. Instead, the
 * number of bits required depends on the maximal number of successors of a node
 * of the graph. As the computations involved to access a decision for a node
 * of the graph is more complex than for {@link SchedulerSimpleArray},
 * operations might be slower.
 * 
 * @author Ernst Moritz Hahn
 */
public final class SchedulerSimpleCompact implements SchedulerSimple {
    /** String containing opening square brackets. */
    private final static String SQUARE_BRACKETS_OPEN = "[";
    /** String containing closing square brackets. */
    private final static String SQUARE_BRACKETS_CLOSE = "]";
    /** String containing a comma. */
    private final static String COMMA = ",";
    /** Log2 of {@link Long#SIZE}. */
    private static final int LOG2LONGSIZE = 6;

    /** Graph this scheduler belongs to. */
    private final GraphExplicit graph;
    /** Number of bits needed to store a scheduler decision for single node. */
    private int numEntryBits;
    /** Decisions for the nodes of the graph. */
    private final long[] content;
    /** Value to get graph property value. */
    private final ValueInteger value;

    /**
     * Constructs a new space-efficient array-based simple scheduler.
     * The scheduler will be constructed for the graph given in the graph
     * parameter. If the content parameter is non-{@code null}, it will be used
     * as the array storing the decisions of the scheduler. Note that the array
     * will not be cloned by the constructor. If the content parameter is
     * @{code null}, a new array will be constructed to store the decisions of
     * the scheduler. The graph parameter must not be @{code null}.
     * 
     * @param graph graph to construct scheduler for
     * @param content array to use for content of scheduler, or {@code null}
     * @throws EPMCException thrown in case of problems during construction
     */
    private SchedulerSimpleCompact(GraphExplicit graph, long[] content) throws EPMCException {
        this.graph = graph;
        int numNodes = graph.getNumNodes();
        int numValues = 0;
        for (int node = 0; node < numNodes; node++) {
            graph.queryNode(node);
            numValues = Math.max(numValues, graph.getNumSuccessors());
        }
        numValues++;
        this.numEntryBits = Integer.SIZE - Integer.numberOfLeadingZeros(numValues - 1);
        int numBits = numEntryBits * graph.getNumNodes();
        int numLongs = ((numBits - 1) >> LOG2LONGSIZE) + 1;
        if (content != null) {
            this.content = content;
        } else {
            this.content = new long[numLongs];
        }
        this.value = TypeInteger.get(graph.getContextValue()).newValue();
    }
    
    /**
     * Construct a new simple simple scheduler.
     * The graph parameter must not be {@code null}.
     * Initially, the decisions for each node are set to
     * {@link Scheduler#UNSET}.
     * 
     * @param graph graph to construct scheduler for
     * @throws EPMCException thrown in case of problems during construction
     */
    public SchedulerSimpleCompact(GraphExplicit graph) throws EPMCException {
        this(graph, null);
    }
    
    @Override
    public GraphExplicit getGraph() {
        return graph;
    }

    @Override
    public void set(int node, int decision) {
        assert assertSet(node, decision);
        decision++;
        for (int bitNr = 0; bitNr < numEntryBits; bitNr++) {
            boolean bitValue = (decision & (1 << bitNr)) != 0;
            int bitIndex = node * numEntryBits + bitNr;
            int offset = bitIndex >> LOG2LONGSIZE;
            if (bitValue) {
                content[offset] |= 1L << bitIndex;
            } else {
                content[offset] &= ~(1L << bitIndex);
            }
        }
    }

    @Override
    public int get(int node) {
        assert node >= 0;
        assert node < graph.getNumNodes();
        int number = 0;
        for (int bitNr = 0; bitNr < numEntryBits; bitNr++) {
            int bitIndex = node * numEntryBits + bitNr;
            int offset = bitIndex >> LOG2LONGSIZE;
            boolean bitValue = (content[offset] & (1L << bitIndex)) != 0;
            if (bitValue) {
                number |= (1 << bitNr);
            }
        }
        number--;
        return number;
    }
    
    /**
     * Function asserting correct call to {@link #set(int, int)}.
     * The method will throw an {@link AssertionError} if the contract of the
     * {@link #set(int, int)} method is violated and assertions are enabled.
     * Otherwise, it will return {@code true}.
     * 
     * @param node node parameter of {@link #set(int, int)}.
     * @param decision decision parameter of {@link #set(int, int)}.
     * @return {@code true} if succeeds
     */
    private boolean assertSet(int node, int decision) {
        assert node >= 0;
        assert node < graph.getNumNodes();
        int previousNode = graph.getQueriedNode();
        try {
            graph.queryNode(node);
        } catch (EPMCException e) {
            e.printStackTrace();
            assert false;
        }
        assert decision >= -1 && decision < graph.getNumSuccessors()
                : decision + " " + node + " " + graph.getNumSuccessors();
        try {
            graph.queryNode(previousNode);
        } catch (EPMCException e) {
            e.printStackTrace();
            assert false;
        }
        return true;
    }

    @Override
    public String toString() {
        StringBuilder builder = new StringBuilder();
        builder.append(SQUARE_BRACKETS_OPEN);
        int numNodes = graph.getNumNodes();
        for (int node = 0; node < numNodes; node++) {
            builder.append(get(node));
            builder.append(COMMA);
        }
        builder.delete(builder.length() - 1, builder.length());
        builder.append(SQUARE_BRACKETS_CLOSE);
        return builder.toString();
    }
    
    @Override
    public SchedulerSimple clone() {
        try {
            return new SchedulerSimpleCompact(graph, content.clone());
        } catch (EPMCException e) {
            e.printStackTrace();
            assert false;
            return null;
        }
    }
    
    @Override
    public Value get() throws EPMCException {
        value.set(get(graph.getQueriedNode()));
        return value;
    }

    @Override
    public void set(Value value) throws EPMCException {
        assert value != null;
        set(graph.getQueriedNode(), ValueInteger.asInteger(value).getInt());
    }

    @Override
    public Type getType() {
        return value.getType();
    }
}
