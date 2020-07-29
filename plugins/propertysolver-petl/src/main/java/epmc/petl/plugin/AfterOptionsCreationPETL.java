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

package epmc.petl.plugin;

import java.util.Map;

import epmc.modelchecker.options.OptionsModelChecker;
import epmc.options.OptionTypeBoolean;
import epmc.options.OptionTypeMap;
import epmc.options.Options;
import epmc.petl.model.ModelMAS;
import epmc.petl.model.PropertyPETL;
import epmc.plugin.AfterOptionsCreation;
import epmc.prism.model.convert.UtilPrismConverter;
import epmc.prism.options.OptionsPRISM;
import epmc.propertysolver.PropertySolverExplicitKnowledge;
import epmc.propertysolver.PropertySolverExplicitPCTLUntilUniform;

public final class AfterOptionsCreationPETL implements AfterOptionsCreation {
    private final static String IDENTIFIER = "after-options-creation-petl";

    @Override
    public String getIdentifier() {
        return IDENTIFIER;
    }

    @Override
    public void process(Options options) {
        assert options != null;
        OptionTypeMap<Class<?>> modelInputType = options.getType(OptionsModelChecker.MODEL_INPUT_TYPE);
        assert modelInputType != null;
        modelInputType.put(ModelMAS.IDENTIFIER, ModelMAS.class);
        Map<String,Class<?>> propertyClasses = options.get(OptionsModelChecker.PROPERTY_CLASS);
        assert propertyClasses != null;
        propertyClasses.put(PropertyPETL.IDENTIFIER, PropertyPETL.class);
        OptionTypeBoolean typeBoolean = OptionTypeBoolean.getInstance();
        options.addOption().setBundleName(OptionsPRISM.PRISM_OPTIONS)
        .setIdentifier(OptionsPRISM.PRISM_FLATTEN)
        .setType(typeBoolean).setDefault(true)
        .setCommandLine().setGui().setWeb().build();
        UtilPrismConverter.addOptions(options);
        
        Map<String,Class<?>> solvers = options.get(OptionsModelChecker.PROPERTY_SOLVER_CLASS);
        solvers.put(PropertySolverExplicitKnowledge.IDENTIFIER, PropertySolverExplicitKnowledge.class);
        solvers.put(PropertySolverExplicitPCTLUntilUniform.IDENTIFIER, PropertySolverExplicitPCTLUntilUniform.class);
    }
}
