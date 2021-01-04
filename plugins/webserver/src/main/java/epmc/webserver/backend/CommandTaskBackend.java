package epmc.webserver.backend;

import epmc.error.EPMCException;
import epmc.modelchecker.CommandTask;
import epmc.webserver.OptionsBackend;
import epmc.options.Options;

public class CommandTaskBackend implements CommandTask {
    final static String IDENTIFIER = "webserver";
//    private Options options;
    
    @Override
    public String getIdentifier() {
        return IDENTIFIER;
    }

    @Override
    public void executeInClientBeforeServer() throws EPMCException {
    	Options options = Options.get();
        String backendProperties = options.getString(OptionsBackend.WEBSERVER_CONFIG);
        String[] args = new String[1];
        args[0] = backendProperties;
        BackendEngine.main(args);
    }
    
    @Override
    public boolean isRunOnServer() {
    	return false;
    }
}
