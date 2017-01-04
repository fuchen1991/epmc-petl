package epmc.jani.model;

import java.io.Serializable;
import java.util.LinkedHashMap;
import java.util.Map;

import javax.json.Json;
import javax.json.JsonObject;
import javax.json.JsonObjectBuilder;
import javax.json.JsonValue;

import epmc.error.EPMCException;
import epmc.expression.Expression;
import epmc.expression.standard.ExpressionLiteral;
import epmc.util.UtilJSON;

/**
 * Location of an automaton.
 * 
 * @author Ernst Moritz Hahn
 */
public final class Location implements JANINode, Serializable {
	/** 1L, as I don't know any better. */
	private static final long serialVersionUID = 1L;
	/** String identifying the name of the location. */
	private final static String NAME = "name";
	/** String identifying time progress condition of this location. */
	private final static String TIME_PROGRESS = "time-progress";
	/** String identifying comment of this location. */
	private final static String COMMENT = "comment";
	/** String identifying state transient values of this location. */
	private final static String TRANSIENT_VALUES = "transient-values";
	
	/** Name of the location. */
	private String name;
	/** Model to which this location belongs. */
	private transient ModelJANI model;
	/** State transient values of this location. */
	private transient Assignments transientValuesAssignments;
	/** Time progress condition of this assignment. */
	private TimeProgress timeProgress;
	/** Comment of this location. */
	private String comment;
	/** Identifiers valid for this location. */
	private Map<String, JANIIdentifier> validIdentifiers;
	
	@Override
	public void setModel(ModelJANI model) {
		this.model = model;
	}

	@Override
	public ModelJANI getModel() {
		return model;
	}
	
	@Override
	public JANINode parse(JsonValue value) throws EPMCException {
		assert model != null;
		assert value != null;
		UtilJSON.ensureObject(value);
		JsonObject object = (JsonObject) value;
		name = UtilJSON.getString(object, NAME);
		// TODO cleanup
		Map<String,JANIIdentifier> validTransientValue = new LinkedHashMap<>();
		validTransientValue.putAll(validIdentifiers);
		transientValuesAssignments = UtilModelParser.parseOptional(model, () -> {
			Assignments assignments = new Assignments();
			assignments.setModel(model);
			assignments.setValidIdentifiers(validTransientValue);
			return assignments;
		}, object, TRANSIENT_VALUES);
		timeProgress = UtilModelParser.parseOptional(model, () -> {
			TimeProgress timeProgress = new TimeProgress();
			timeProgress.setModel(model);
			timeProgress.setIdentifiers(validIdentifiers);
			return timeProgress;
		}, object, TIME_PROGRESS);
		comment = UtilJSON.getStringOrNull(object, COMMENT);
		return this;
	}

	@Override
	public JsonValue generate() throws EPMCException {
		JsonObjectBuilder result = Json.createObjectBuilder();
		result.add(NAME, name);
		UtilModelParser.addOptional(result, TRANSIENT_VALUES, transientValuesAssignments);
		UtilModelParser.addOptional(result, TIME_PROGRESS, timeProgress);
		UtilJSON.addOptional(result, COMMENT, comment);
		return result.build();
	}
	
	/**
	 * Set name of this location.
	 * 
	 * @param name name of location to set
	 */
	public void setName(String name) {
		this.name = name;
	}
	
	/**
	 * Get the name of the location.
	 * 
	 * @return name of the location
	 */
	public String getName() {
		return name;
	}

	/**
	 * Set time progress condition of this location
	 * 
	 * @param timeProgress time progress condition to set for this location
	 */
	public void setTimeProgress(TimeProgress timeProgress) {
		this.timeProgress = timeProgress;
	}
	
	/**
	 * Get time progress condition of this location.
	 * 
	 * @return timeProgress of this location
	 */
	public TimeProgress getTimeProgress() {
		return timeProgress;
	}
	
	/**
	 * Get expression of time progress condition  or {@code true}.
	 * If the time progress condition is set, its expression
	 * {@link TimeProgress#getExp()} will be returned. Otherwise, the {@code true}
	 * expression will be returned.
	 * 
	 * @return expression of time progress condition or {@code true}
	 */
	public Expression getTimeProgressExpressionOrTrue() {
		if (timeProgress == null) {
			return ExpressionLiteral.getTrue(model.getContextValue());
		} else {
			return timeProgress.getExp();
		}
	}
	
	public Assignments getTransientValueAssignmentsOrEmpty() {
		Assignments result;
		if (transientValuesAssignments == null) {
			result = new Assignments();
			result.setModel(model);
		} else {
			result = transientValuesAssignments;
		}
		return result;
	}
	
	/**
	 * Get state transient values of this location.
	 * 
	 * @return state transient values of this location
	 */
	public Assignments getTransientValueAssignments() {
		return transientValuesAssignments;
	}
	
	public void setTransientValueAssignments(Assignments transientValueAssignments) {
		this.transientValuesAssignments = transientValueAssignments;
	}

	public void setValidIdentifiers(Map<String, JANIIdentifier> validIdentifiers) {
		this.validIdentifiers = validIdentifiers;
	}
	
	@Override
	public String toString() {
		return UtilModelParser.toString(this);
	}
}
