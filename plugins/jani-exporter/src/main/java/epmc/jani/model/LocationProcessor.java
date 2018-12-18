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

package epmc.jani.model;

import javax.json.Json;
import javax.json.JsonObjectBuilder;
import javax.json.JsonValue;

import epmc.jani.exporter.processor.JANIProcessor;
import epmc.jani.exporter.processor.ProcessorRegistrar;

public class LocationProcessor implements JANIProcessor {
    /** String identifying the name of the location. */
    private final static String NAME = "name";
    /** String identifying time progress condition of this location. */
    private final static String TIME_PROGRESS = "time-progress";
    /** String identifying comment of this location. */
    private final static String COMMENT = "comment";
    /** String identifying state transient values of this location. */
    private final static String TRANSIENT_VALUES = "transient-values";

    private Location location = null;

    @Override
    public JANIProcessor setElement(Object component) {
        assert component != null;
        assert component instanceof Location; 

        location = (Location) component;
        return this;
    }

    @Override
    public JsonValue toJSON() {
        assert location != null;

        JsonObjectBuilder builder = Json.createObjectBuilder();
        
        builder.add(NAME, location.getName());
        
        Assignments transientValuesAssignments = location.getTransientValueAssignments();
        if (transientValuesAssignments != null) {
            builder.add(TRANSIENT_VALUES, ProcessorRegistrar.getProcessor(transientValuesAssignments)
                    .toJSON());
        }
        
        TimeProgress timeProgress = location.getTimeProgress();
        if (timeProgress != null) {
            builder.add(TIME_PROGRESS, ProcessorRegistrar.getProcessor(timeProgress)
                    .toJSON());
        }

        String comment = location.getComment();
        if (comment != null) {
            builder.add(COMMENT, comment);
        }
        
        return builder.build();
    }
}
