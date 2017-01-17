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

package epmc.jani.extensions.trigonometricfunctions;

import epmc.error.EPMCException;
import epmc.jani.model.JANINode;
import epmc.jani.model.JANIOperators;
import epmc.jani.model.ModelExtension;
import epmc.jani.model.ModelJANI;

public final class ModelExtensionTrigonometricFunctions implements ModelExtension {
	public final static String IDENTIFIER = "trigonometric-functions";
	private ModelJANI model;
	private JANINode node;

	@Override
	public String getIdentifier() {
		return IDENTIFIER;
	}

	@Override
	public void setModel(ModelJANI model) throws EPMCException {
		this.model = model;
	}

	@Override
	public void setNode(JANINode node) throws EPMCException {
		this.node = node;
	}

	@Override
	public void parseBefore() throws EPMCException {
		if (!(this.node instanceof ModelJANI)) {
			return;
		}
		JANIOperators operators = model.getJANIOperators();
		operators.add()
			.setArity(1)
			.setEPMC(OperatorSin.IDENTIFIER)
			.setJANI(OperatorSin.IDENTIFIER)
			.build();
		operators.add()
			.setArity(1)
			.setEPMC(OperatorCos.IDENTIFIER)
			.setJANI(OperatorCos.IDENTIFIER)
			.build();
		operators.add()
			.setArity(1)
			.setEPMC(OperatorTan.IDENTIFIER)
			.setJANI(OperatorTan.IDENTIFIER)
			.build();
		
		operators.add()
			.setArity(1)
			.setEPMC(OperatorAsin.IDENTIFIER)
			.setJANI(OperatorAsin.IDENTIFIER)
			.build();
		operators.add()
			.setArity(1)
			.setEPMC(OperatorAcos.IDENTIFIER)
			.setJANI(OperatorAcos.IDENTIFIER)
			.build();
		operators.add()
			.setArity(1)
			.setEPMC(OperatorAtan.IDENTIFIER)
			.setJANI(OperatorAtan.IDENTIFIER)
			.build();
	}
}