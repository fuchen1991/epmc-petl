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

package epmc.jani.explorer;

import epmc.error.EPMCException;
import epmc.graph.explorer.Explorer;
import epmc.value.Type;
import epmc.value.Value;

public final class PropertyEdgeTransientValue implements PropertyEdge {
	private final ExplorerJANI explorer;
	private final int varNr;
	private final Type type;

	PropertyEdgeTransientValue(ExplorerJANI explorer, int varNr) throws EPMCException {
		assert explorer != null;
		assert varNr >= 0;
		this.explorer = explorer;
		this.varNr = varNr;
		this.type = explorer.getStateVariables().getType(explorer.getStateVariables().getVariables().get(varNr));
	}
	
	@Override
	public Explorer getExplorer() {
		return explorer;
	}

	@Override
	public Value get(int successor) throws EPMCException {
		return explorer.getSuccessorNode(successor).getValue(varNr);
	}

	@Override
	public Type getType() {
		return type;
	}	
}