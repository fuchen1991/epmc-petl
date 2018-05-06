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

package epmc.petl.model;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import epmc.expression.Expression;

/**
 * Storing the expressions representing the equivalence classes
 * 
 * @author Chen Fu
 */

public class EquivalenceRelations {
	private Map<String, List<Expression>> equivalenceRelations;
	
	public EquivalenceRelations() {
		equivalenceRelations = new HashMap<String, List<Expression>>();
	}
	
	public EquivalenceRelations(Map<String, List<Expression>> equivalenceRelations) {
		this.equivalenceRelations  = equivalenceRelations;
	}

	public Map<String, List<Expression>> getEquivalenceRelations() {
		return equivalenceRelations;
	}
	
	public void addRelation(String moduleName, Expression exp) {
		List<Expression> expList = equivalenceRelations.get(moduleName);
		if(expList == null)
		{
			expList = new ArrayList<Expression>();
			equivalenceRelations.put(moduleName, expList);
		}
		
		expList.add(exp);
	}
	public Set<Expression> getAllExpressions()
	{
		Set<Expression> res = new HashSet<Expression>();
		for(List<Expression> list : equivalenceRelations.values())
		{
			for(Expression exp : list)
			{
				res.add(exp);
			}
		}
		
		return res;
	}
	
	@Override
    public String toString() {
        StringBuilder builder = new StringBuilder();
        builder.append("Equivalence Relations:\n");
        for (Entry<String, List<Expression>> entry : equivalenceRelations.entrySet()) {
        	builder.append("  " + entry.getKey() + "\n");
        	List<Expression> expList = entry.getValue();
        	for(Expression exp : expList)
        	{
        		builder.append("  " + exp.toString() + "\n");
        	}
        }

        return builder.toString();
    }
}
