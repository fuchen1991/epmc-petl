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

import epmc.prism.exporter.processor.JANI2PRISMProcessorStrict;
import epmc.prism.exporter.processor.ProcessorRegistrar;

public class LocationProcessor implements JANI2PRISMProcessorStrict {

    private Location location = null;

    @Override
    public JANI2PRISMProcessorStrict setElement(Object obj) {
        assert obj != null;
        assert obj instanceof Location; 

        location = (Location) obj;
        return this;
    }

    @Override
    public String toPRISM() {
        assert location != null;

        return "";
    }

    @Override
    public void validateTransientVariables() {
        assert location != null;

        TimeProgress timeProgress = location.getTimeProgress();
        if (timeProgress != null) {
            ProcessorRegistrar.getProcessor(timeProgress)
                .validateTransientVariables();
        }
        for (AssignmentSimple assignment : location.getTransientValueAssignmentsOrEmpty()) {
            ProcessorRegistrar.getProcessor(assignment)
                .validateTransientVariables();
        }
    }

    @Override
    public boolean usesTransientVariables() {
        assert location != null;

        boolean usesTransient = false;
        TimeProgress timeProgress = location.getTimeProgress();
        if (timeProgress != null) {
            usesTransient |= ProcessorRegistrar.getProcessor(timeProgress)
                    .usesTransientVariables();
        }
        for (AssignmentSimple assignment : location.getTransientValueAssignmentsOrEmpty()) {
            usesTransient |= ProcessorRegistrar.getProcessor(assignment)
                    .usesTransientVariables();
        }

        return usesTransient;
    }	
}
