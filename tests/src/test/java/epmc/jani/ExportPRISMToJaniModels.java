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

package epmc.jani;

import static epmc.ModelNamesPRISM.*;
import static epmc.jani.ModelNames.*;
import static epmc.modelchecker.TestHelper.prepare;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;

import javax.json.JsonValue;

import org.junit.BeforeClass;
import org.junit.Test;

import epmc.jani.model.ModelJANI;
import epmc.jani.model.ModelJANIConverter;
import epmc.modelchecker.TestHelper;
import epmc.options.Options;
import epmc.util.UtilJSON;

public final class ExportPRISMToJaniModels {
    /**
     * Set up the tests.
     */
    @BeforeClass
    public static void initialise() {
        prepare();
    }

    @Test
    public void convertTest() {
        export(System.getProperty("user.home") + "/test.prism", System.getProperty("user.home") + "/test.prop", System.getProperty("user.home") + "/test.jani");
    }

    @Test
    public void convertSingle() {
        export(String.format(COIN_MODEL, 2), COIN_PROPERTY);
    }

    @Test
    public void convertPRISMIncluded() {
        export(BRP_MODEL, BRP_PROPERTY);
        export(CELL_MODEL, CELL_PROPERTY);
        export(CLUSTER_MODEL, CLUSTER_PROPERTY);
        for (int i : new int[]{2,4,6,8,10}) {
            export(String.format(COIN_MODEL, i), COIN_PROPERTY);
        }
        for (int i : new int[]{2,3,4}) {
            for (int j : new int[]{2,4,6}) {
                export(String.format(CSMA_MODEL, i, j), CSMA_PROPERTY);
            }
        }
        export(DICE_MODEL, DICE_PROPERTY);
        export(TWO_DICE_MODEL, TWO_DICE_PROPERTY);
        for (int i : new int[]{3,4,5,6,7,8,9,10,15}) {
            export(String.format(DINING_CRYPT_MODEL, i), DINING_CRYPT_PROPERTY);
        }
        //    	export(EMBEDDED_MODEL, EMBEDDED_PROPERTY);
        export(FIREWIRE_ABST_MODEL, FIREWIRE_ABST_PROPERTY, JANI_EXPORT_DIR + "firewire_abs" + JANI_EXTENSION);
        export(FIREWIRE_IMPL_MODEL, FIREWIRE_IMPL_PROPERTY, JANI_EXPORT_DIR + "firewire_impl" + JANI_EXTENSION);
        export(FMS_MODEL, FMS_PROPERTY);
        export(KANBAN_MODEL, KANBAN_PROPERTY);
        //Before enabling this test, fix the LEADER_ASYNC_PROPERTY file since it contains
        //the wrong property   fiter(forall, leaders<=1)  instead of the correct one
        //  filter(forall, leaders<=1)  
        for (int i : new int[]{3,4,5,6,7,8,9,10}) {
            export(String.format(LEADER_ASYNC_MODEL, i), LEADER_ASYNC_PROPERTY,
                    String.format(JANI_EXPORT_DIR + "leader_async_%d" + JANI_EXTENSION, i));
        }
        for (int i : new int[]{3,4,5,6}) {
            for (int j : new int[]{2,3,4,5,6,8}) {
                export(String.format(LEADER_SYNC_MODEL, i, j), LEADER_SYNC_PROPERTY, 
                        String.format(JANI_EXPORT_DIR + "leader_sync_%d_%d" + JANI_EXTENSION, i, j));
            }
        }
        export(KNACL_MODEL, KNACL_PROPERTY);
        export(NACL_MODEL, NACL_PROPERTY);
        export(MC_MODEL, MC_PROPERTY);
        for (int i : new int[]{3,4,5,8,10}) {
            export(String.format(MUTUAL_MODEL, i), MUTUAL_PROPERTY);
        }
        for (int i : new int[]{4,5}) {
            for (int j : new int[]{4,5,6,7,8}) {
                export(String.format(PEER2PEER_MODEL, i, j), PEER2PEER_PROPERTY);
            }
        }
        for (int i : new int[]{3,4,5,6,7,8,9,10,15,20,25,30}) {
            export(String.format(PHIL_MODEL, i), PHIL_PROPERTY);
        }
        for (int i : new int[]{3,4,5,6,7,8,9,10}) {
            export(String.format(PHIL_NOFAIR_MODEL, i), String.format(PHIL_NOFAIR_PROPERTY, i));
        }
        for (int i : new int[]{3,4}) {
            export(String.format(PHIL_LSS_MODEL, i), String.format(PHIL_LSS_PROPERTY, i));
        }
        for (int i : new int[]{2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20}) {
            export(String.format(POLLING_MODEL, i), POLLING_PROPERTY);
        }
        for (int i : new int[]{3,4,5,6,7,8,9,10}) {
            export(String.format(RABIN_MODEL, i), RABIN_PROPERTY);
        }
        for (int i : new int[]{3,5,7,9,11}) {
            export(String.format(BEAUQUIER_MODEL, i), BEAUQUIER_PROPERTY);
        }
        for (int i : new int[]{3,5,7,9,11,13,15,17,19,21}) {
            export(String.format(HERMAN_MODEL, i), HERMAN_PROPERTY);
        }
        for (int i : new int[]{3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21}) {
            export(String.format(IJ_MODEL, i), IJ_PROPERTY);
        }
        export(TANDEM_MODEL, TANDEM_PROPERTY);
        for (int i : new int[]{0,1,2,3,4,5,6}) {
            export(String.format(WLAN_MODEL, i), WLAN_PROPERTY);
        }
        for (int i : new int[]{0,1,2,3,4,5,6}) {
            export(String.format(WLAN_COLLIDE_MODEL, i), WLAN_COLLIDE_PROPERTY);
        }
        for (int i : new int[]{0,1,2,3,4,5,6}) {
            export(String.format(WLAN_TIME_BOUNDED_MODEL, i), WLAN_TIME_BOUNDED_PROPERTY);
        }
        export(ZEROCONF_MODEL, ZEROCONF_PROPERTY);
        export(ZEROCONF_TIME_BOUNDED_MODEL, ZEROCONF_TIME_BOUNDED_PROPERTY);
    }

    //    @Test
    public void convertPRISMHomepage() {
        //    	export(BROADCAST_COLL_ASYNC_MODEL);
        //    	export(BROADCAST_COLL_SYNC_MODEL);
        //    	export(BROADCAST_COLL_SYNC_DELAY_MODEL);
        //    	export(BROADCAST_COLL_SYNC_LOSSY_MODEL);
        //    	export(BROADCAST_NO_COLL_SYNC_MODEL);
        export(String.format(BYZANTINE_MODEL, 4, 1));
        export(CC_EDF_MODEL);
        export(CIRCADIAN_MODEL);
        export(CONTRACT_BMGR_MODEL);
        export(CROWDS_MODEL);
        export(CYCLIN_MODEL);
        export(String.format(FAIR_EXCHANGE_MODEL, 10));
        export(FGF_MODEL);
        export(String.format(GOSSIP_MODEL, 4));
        export(String.format(GRAPH_MODEL, 4));
        export(INVESTOR_MODEL);
        export(KAMINSKY_MODEL);
        export(MAPK_CASCADE_MODEL);
        export(MDPTT_MODEL);
        // export(MDSM_MODEL);
        // export(MDSM_P_MODEL);
        export(NAND_MODEL);
        export(NEGOTIATION_MODEL);
        export(OPTIMAL_TWO_DICE_MODEL);
        export(PINCRACKING_MODEL);
        // POWER_CTMC3_PM1_MODEL
        // POWER_CTMC3_SP_MODEL
        // POWER_CTMC3_SR_MODEL
        // POWER_CTMC4_PM1_MODEL
        // POWER_CTMC4_SP_MODEL
        // (POWER_CTMC4_SR_MODEL
        // POWER_DTMC_BATTERY_MODEL
        // POWER_DTMC_CLOCK_MODEL
        // POWER_DTMC_PM_MODEL
        // POWER_DTMC_REWARDS_MODEL
        // POWER_DTMC_SP_MODEL
        // POWER_DTMC_SR_MODEL
        // POWER_DTMC_SRQ_MODEL
        export(RABIN_CHOICE_MODEL);
        export(ROBOT_MODEL);
        for (int i : new int[]{1,2,3}) {
            export(String.format(STABLE_MATCHING_MODEL, i));
        }
        export(STATIC_EDF_MODEL);
        export(TEST_AND_SET_MODEL);
        export(THINKTEAM_RETRIAL_MODEL);
        // export(UAV_GAME_MODEL);
        export(UAV_MDP_MODEL);
        export(String.format(VIRUS_MODEL, 3));
        export(WALKERS_RING_LL_MODEL);
    }

    private static void export(String prismFilename) {
        export(prismFilename, null, null);
    }

    private static void export(String prismFilename, String propertyFilename) {
        export(prismFilename, propertyFilename, null);
    }

    private static void export(String prismFilename, String propertyFilename, String janiFilename) {
        String modelName = new File(prismFilename).getName();
        modelName = modelName.substring(0, modelName.lastIndexOf('.'));
        if (janiFilename == null) {
            janiFilename = getJANIFilenameFromPRISMFilename(prismFilename);
        }
        System.out.println("Exporting " + prismFilename + ":");
        System.out.println("Loading");
        Options options = ConvertTestConfiguration.prepareJANIOptions(null);
        options.set("prism-flatten", false);
        ModelJANIConverter prism;
        if (propertyFilename == null) {
            prism = (ModelJANIConverter) TestHelper.loadModel(options, prismFilename);
        } else {
            prism = (ModelJANIConverter) TestHelper.loadModel(options, prismFilename, propertyFilename);
        }
        System.out.println("Converting");       
        ModelJANI jani = prism.toJANI(true);
        jani.setName(modelName);
        System.out.println("Generating JSON");
        JsonValue json = jani.generate();
        System.out.println("Writing " + janiFilename);
        try (PrintWriter out = new PrintWriter(janiFilename)) {
            out.println(UtilJSON.prettyString(json));
        } catch (FileNotFoundException e) {
            throw new RuntimeException(e);
        }
        System.out.println("Done");
        System.out.println();
    }
}
