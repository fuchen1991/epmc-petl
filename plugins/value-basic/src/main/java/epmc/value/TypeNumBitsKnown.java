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

package epmc.value;

import epmc.value.Type;

public interface TypeNumBitsKnown extends Type {
    static int UNKNOWN = Integer.MAX_VALUE;

    static boolean isNumBitsKnown(Type type) {
        if (!(type instanceof TypeNumBitsKnown)) {
            return false;
        }
        TypeNumBitsKnown typeNumBitsKnown = (TypeNumBitsKnown) type;
        if (typeNumBitsKnown.getNumBits() == UNKNOWN) {
            return false;
        }
        return true;
    }

    static TypeNumBitsKnown asNumBitsKnown(Type type) {
        if (isNumBitsKnown(type)) {
            return (TypeNumBitsKnown) type;
        } else {
            return null;
        }
    }

    static int getNumBits(Type type) {
        TypeNumBitsKnown typeNumBitsKnown = TypeNumBitsKnown.asNumBitsKnown(type);
        if (typeNumBitsKnown != null) {
            return typeNumBitsKnown.getNumBits();
        } else {
            return UNKNOWN;
        }
    }

    int getNumBits();
}
