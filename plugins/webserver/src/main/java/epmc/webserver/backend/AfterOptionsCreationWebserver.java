package epmc.webserver.backend;

import java.util.Map;

import epmc.error.EPMCException;
import epmc.main.options.OptionsEPMC;
import epmc.modelchecker.CommandTask;
import epmc.options.OptionTypeInteger;
import epmc.options.OptionTypeString;
import epmc.options.Options;
import epmc.plugin.AfterOptionsCreation;
import epmc.webserver.OptionsBackend;

public final class AfterOptionsCreationWebserver implements AfterOptionsCreation {
	public final static String IDENTIFIER = "webserver";
	
	@Override
	public String getIdentifier() {
		return IDENTIFIER;
	}

	@Override
	public void process(Options options) throws EPMCException {
		Map<String,Class<? extends CommandTask>> commandTaskClasses = options.get(OptionsEPMC.COMMAND_CLASS);
        assert commandTaskClasses != null;

		OptionTypeString typeString = OptionTypeString.getInstance();
		
		options.addCommand()
        .setBundleName(OptionsBackend.WEBSERVER_OPTIONS)
        .setIdentifier(CommandTaskBackend.IDENTIFIER)
        .setCommandLine()
        .setGui()
        .setWeb().build();
        commandTaskClasses.put(OptionsBackend.WEBSERVER.name().toLowerCase(), CommandTaskBackend.class);
        
        options.addCommand()
        .setBundleName(OptionsBackend.WEBSERVER_OPTIONS)
        .setIdentifier(CommandTaskServer.IDENTIFIER)
        .setCommandLine()
        .setGui()
        .setWeb().build();
        commandTaskClasses.put(OptionsBackend.SERVER.name().toLowerCase(), CommandTaskServer.class);
        
        options.addOption()
        .setBundleName(OptionsBackend.WEBSERVER_OPTIONS)
        .setIdentifier(OptionsBackend.WEBSERVER_CONFIG)
        .setType(typeString)
        .setDefault(null)
        .setCommandLine().setGui().setWeb()
        .build();
        
        
        options.addOption()
        .setBundleName(OptionsBackend.WEBSERVER_OPTIONS)
        .setIdentifier(OptionsBackend.SERVER_NAME)
        .setType(typeString)
        .setDefault("")
        .setCommandLine().setGui().setWeb()
        .build();
        
        OptionTypeInteger typeInt = OptionTypeInteger.getInstance();
        options.addOption()
        .setBundleName(OptionsBackend.WEBSERVER_OPTIONS)
        .setIdentifier(OptionsBackend.SERVER_PORT)
        .setType(typeInt)
        .setDefault(10000)
        .setCommandLine().setGui().setWeb()
        .build();
	}

}
