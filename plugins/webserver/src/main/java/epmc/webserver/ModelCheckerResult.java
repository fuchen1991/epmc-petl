package epmc.webserver;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import epmc.modelchecker.RawProperty;

public class ModelCheckerResult implements Serializable {
    private static final long serialVersionUID = 1L;
    private Object commonResult;
    private final Map<RawProperty,Object> results = new LinkedHashMap<>();
    private final List<Object> resultList = new ArrayList<>();
    private final List<Object> publicResultList =
            Collections.unmodifiableList(resultList);
    
    public void set(Object commonResult) {
        assert commonResult != null;
        this.commonResult = commonResult;
    }
    
    public Object getCommonResult() {
        return commonResult;
    }

    public String getCommonResultString() {
        if (commonResult == null) {
            return null;
        }
        return commonResult.toString();
    }

    public void add(RawProperty property, Object result) {
        assert property != null;
        assert result != null;
        results.put(property, result);
        resultList.add(result);
    }

    public Object get(RawProperty property) {
        assert property != null;
        return results.get(property);
    }
    
    public String getString(RawProperty property) {
        assert property != null;
        Object get = get(property);
        if (get == null) {
            return null;
        }
        return get.toString();
    }

    @Override
    public String toString() {
        StringBuilder builder = new StringBuilder();
        builder.append("Results:\n");
        for (Entry<RawProperty,Object> entry : results.entrySet()) {
            builder.append("  ");
            builder.append(entry.getKey().getDefinition());
            builder.append(": ");
            builder.append(entry.getValue());
            builder.append("\n");
        }
        return builder.toString();
    }
    
    public List<Object> getResultList() {
        return publicResultList;
    }

    public Collection<RawProperty> getProperties() {
        return results.keySet();
    }
}
