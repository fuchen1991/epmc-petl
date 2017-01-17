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

package epmc.util;

import org.junit.Test;

import epmc.error.EPMCException;
import epmc.main.options.UtilOptionsEPMC;
import epmc.options.Options;
import epmc.plugin.UtilPlugin;

public class OptionsTest {

    @Test
    public void testOptions() throws EPMCException {
        Options options;

        // had some crashes when no arguments were present
        String[] noArgs = {};
        options = UtilOptionsEPMC.newOptions();
        options.parseOptions(noArgs, true);
        options.reset();
        UtilPlugin.loadPlugins(options);
        options.parseOptions(noArgs, false);

        String[] helpArgs = {"help"};
        
        options = UtilOptionsEPMC.newOptions();
        options.parseOptions(helpArgs, true);
        options.reset();
        UtilPlugin.loadPlugins(options);
        options.parseOptions(helpArgs, false);

        options.getShortUsage();
        // check whether we forgot to specify resource strings
//        options.getUsage();
    }

}