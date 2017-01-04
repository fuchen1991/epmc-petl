package epmc.jani.model.component;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;

import javax.json.Json;
import javax.json.JsonArray;
import javax.json.JsonArrayBuilder;
import javax.json.JsonObject;
import javax.json.JsonObjectBuilder;
import javax.json.JsonValue;

import epmc.error.EPMCException;
import epmc.jani.model.Action;
import epmc.jani.model.JANINode;
import epmc.jani.model.ModelJANI;
import epmc.jani.model.UtilModelParser;
import epmc.util.UtilJSON;

/**
 * Rename system component.
 * This system component is responsible for renaming the actions (but not the
 * variables) of another system component.
 * 
 * @author Ernst Moritz Hahn
 */
public final class ComponentRename implements Component {
	public final static String IDENTIFIER = "rename";
	/** String identifying the object as a composition systems. */
	private final static String COMPOSITION = "composition";
	/** String identifying the composition as a rename composition. */
	private final static String RENAME = "rename";
	/** String identifying the element of the model to be renamed. */
	private final static String ELEMENT = "element";
	/** String identifying the map of renaming actions. */
	private final static String MAP = "map";
	/** String identifying the actions which are to be renamed. */
	private final static String FROM = "from";
	/** String identifying the actions to which the "from" actions are renamed. */
	private final static String TO = "to";
	private final static String COMMENT = "comment";

	/** System component the actions of which are being renamed. */
	private Component renamed;
	/** Map from actions being renamed to substitute. */
	private final Map<Action,Action> renaming = new LinkedHashMap<>();
	/** Unmodifiable map from actions being renamed to substitute. */
	private final Map<Action,Action> renamingExternal = Collections.unmodifiableMap(renaming);
	private ModelJANI model;
	private String comment;

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
		UtilJSON.ensureEquals(object, COMPOSITION, RENAME);
		UtilJSON.ensurePresent(object.get(ELEMENT), ELEMENT);
		SystemParser system = new SystemParser();
		system.setModel(model);
		system.parse(object.get(ELEMENT));
		renamed = system.getSystemComponent();
		JsonArray map = UtilJSON.getArrayObject(object, MAP);
		for (JsonObject entry : map.getValuesAs(JsonObject.class)) {
			Action from = UtilJSON.toOneOf(object, FROM, model.getActionsOrEmpty());
			Action to = model.getSilentAction();
			UtilJSON.ensureUnique(from, renaming);
			if (entry.containsKey(TO)) {
				to = UtilJSON.toOneOf(object, TO, model.getActionsOrEmpty());
			}
			renaming.put(from, to);
		}
		comment = UtilJSON.getStringOrNull(object, COMMENT);
		return this;
	}

	public void addRenaming(Action from, Action to) {
		renaming.put(from, to);
	}
	
	public void addRenamings(Map<Action,Action> renaming) {
		this.renaming.putAll(renaming);
	}
	
	@Override
	public JsonValue generate() throws EPMCException {
		JsonObjectBuilder result = Json.createObjectBuilder();
		result.add(COMPOSITION, RENAME);
		result.add(ELEMENT, renamed.generate());
		JsonArrayBuilder fromB = Json.createArrayBuilder();
		JsonArrayBuilder toB = Json.createArrayBuilder();
		for (Entry<Action, Action> entry : renaming.entrySet()) {
			fromB.add(entry.getKey().getName());
			toB.add(entry.getValue().getName());
		}
		result.add(FROM, fromB.build());
		result.add(TO, toB.build());
		UtilJSON.addOptional(result, COMMENT, comment);
		return result.build();
	}

	public void setComment(String comment) {
		this.comment = comment;
	}
	
	public String getComment() {
		return comment;
	}
	
	public void setRenamed(Component renamed) {
		this.renamed = renamed;
	}
	
	/**
	 * Get the component the actions of which are to be renamed.
	 * 
	 * @return component the actions of which are to be renamed
	 */
	public Component getRenamed() {
		return renamed;
	}
	
	/**
	 * Obtain map from old actions to renamed actions.
	 * The map returned is unmodifiable.
	 * 
	 * @return map from old actions to renamed actions
	 */
	public Map<Action, Action> getRenaming() {
		return renamingExternal;
	}
	
	@Override
	public String toString() {
		return UtilModelParser.toString(this);
	}
}
