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

import java.util.Arrays;

import epmc.value.Value;
import epmc.value.ValueArray;

final class ValueArrayTernary implements ValueArray {
    private static final int LOG2LONGSIZE = 6;
    private final TypeArrayTernary type;
    private long[] content;
    private int size;

    ValueArrayTernary(TypeArrayTernary type) {
        assert type != null;
        this.type = type;
        int numBits = size() * getBitsPerEntry();
        int numLongs = ((numBits - 1) >> LOG2LONGSIZE) + 1;
        this.content = new long[numLongs];
    }

    private int getBitsPerEntry() {
        return getType().getEntryType().getNumBits();
    }

    @Override
    public void set(Value value, int index) {
        assert value != null;
        assert index >= 0;
        assert index < size();
        ValueTernary valueTernary = (ValueTernary) value;
        int number = valueTernary.getTernary().ordinal();
        for (int bitNr = 0; bitNr < getBitsPerEntry(); bitNr++) {
            boolean bitValue = (number & (1 << bitNr)) != 0;
            int bitIndex = index * getBitsPerEntry() + bitNr;
            int offset = bitIndex >> LOG2LONGSIZE;
            if (bitValue) {
                content[offset] |= 1L << bitIndex;
            } else {
                content[offset] &= ~(1L << bitIndex);
            }
        }
    }

    @Override
    public void get(Value value, int index) {
        assert value != null;
        assert index >= 0;
        assert index < size();
        int number = 0;
        for (int bitNr = 0; bitNr < getBitsPerEntry(); bitNr++) {
            int bitIndex = index * getBitsPerEntry() + bitNr;
            int offset = bitIndex >> LOG2LONGSIZE;
        boolean bitValue = (content[offset] & (1L << bitIndex)) != 0;
        if (bitValue) {
            number |= (1 << bitNr);
        }
        }
        ValueTernary.as(value).set(Ternary.values()[number]);
    }

    @Override
    public TypeArrayTernary getType() {
        return type;
    }

    @Override
    public int hashCode() {
        int hash = 0;
        hash = Arrays.hashCode(content) + (hash << 6) + (hash << 16) - hash;
        return hash;
    }

    @Override
    public void setSize(int size) {
        assert size >= 0;
        int numBits = size * getBitsPerEntry();
        int num = ((numBits - 1) >> LOG2LONGSIZE) + 1;
        this.content = new long[num];
        this.size = size;
    }

    @Override
    public int size() {
        return size;
    }

    @Override
    public String toString() {
        return UtilValue.arrayToString(this);
    }
}
