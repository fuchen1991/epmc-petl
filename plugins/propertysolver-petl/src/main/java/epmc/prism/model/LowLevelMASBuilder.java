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

package epmc.prism.model;

import java.util.LinkedHashSet;
import java.util.Set;

import epmc.expression.standard.ExpressionIdentifier;
import epmc.expression.standard.ExpressionIdentifierStandard;
import epmc.expression.standard.RewardSpecification;
import epmc.expression.standard.RewardSpecificationImpl;
import epmc.graph.LowLevel;
import epmc.graph.LowLevel.Builder;
import epmc.jani.model.ModelJANI;
import epmc.modelchecker.Engine;
import epmc.modelchecker.EngineDD;
import epmc.modelchecker.EngineExplicit;
import epmc.modelchecker.EngineExplorer;
import epmc.modelchecker.Model;
import epmc.modelchecker.UtilModelChecker;
import epmc.prism.model.convert.PRISM2JANIConverter;

public class LowLevelMASBuilder implements LowLevel.Builder {

	public final static String IDENTIFIER = "mas";
    
    private Model model;
    private Engine engine;
    private Set<Object> graphProperties = new LinkedHashSet<>();
    private Set<Object> nodeProperties = new LinkedHashSet<>();
    private Set<Object> edgeProperties = new LinkedHashSet<>();
    
    @Override
    public Builder setModel(Model model) {
        this.model = model;
        return this;
    }

    @Override
    public Builder setEngine(Engine engine) {
        this.engine = engine;
        return this;
    }

    @Override
    public Builder addGraphProperties(Set<Object> graphProperties) {
        this.graphProperties.addAll(graphProperties);
        return this;
    }

    @Override
    public Builder addNodeProperties(Set<Object> nodeProperties) {
        this.nodeProperties.addAll(nodeProperties);
        return this;
    }

    @Override
    public Builder addEdgeProperties(Set<Object> edgeProperties) {
        this.edgeProperties.addAll(edgeProperties);
        return this;
    }

    private Set<Object> fixProperties(Set<Object> properties) {
        Set<Object> fixed = new LinkedHashSet<>(properties.size());
        for (Object property : properties) {
            if (property instanceof RewardSpecification) {
                RewardSpecification rewardSpecification = (RewardSpecification) property;
                RewardStructure rewardStructure = ((ModelPRISM) model).getReward(rewardSpecification);
                ExpressionIdentifier rewardName = new ExpressionIdentifierStandard.Builder()
                        .setName(rewardStructure.getName())
                        .build();
                RewardSpecification fixedRewardSpecification = new RewardSpecificationImpl(rewardName);             
                fixed.add(fixedRewardSpecification);
            } else {
                fixed.add(property);
            }
        }
        return fixed;
    }

    public ModelJANI toJANI(boolean forExporting) {
        PRISM2JANIConverter converter = new PRISM2JANIConverter( ((ModelMAS)model).synModelPrism, forExporting);
        return converter.convert();
    }

    @Override
    public LowLevel build() {
        if (!(model instanceof ModelMAS)) {
            return null;
        }
        graphProperties = fixProperties(graphProperties);
        nodeProperties = fixProperties(nodeProperties);
        edgeProperties = fixProperties(edgeProperties);
        if (engine instanceof EngineExplorer
                || engine instanceof EngineExplicit) {
            ModelJANI jani = toJANI(false);
            return UtilModelChecker.buildLowLevel(jani, engine,
                    graphProperties, nodeProperties, edgeProperties);
        } else if (engine instanceof EngineDD){
            ((ModelPRISM) model).prepareAndCheckReady();
            return new GraphDDPRISM((ModelPRISM) model, nodeProperties, edgeProperties);
        } else {
            return null;
        }
    }

}
