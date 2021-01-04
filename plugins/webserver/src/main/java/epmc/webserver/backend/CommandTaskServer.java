package epmc.webserver.backend;

import java.rmi.RemoteException;
import java.rmi.registry.LocateRegistry;
import java.rmi.registry.Registry;
import epmc.error.EPMCException;
import epmc.error.Problem;

import epmc.main.options.OptionsEPMC;
import epmc.modelchecker.CommandTask;
import epmc.modelchecker.ModelChecker;
import epmc.options.Options;
import epmc.value.ContextValue;
import epmc.webserver.EPMCRemote;
import epmc.webserver.EPMCServer;
import epmc.webserver.OptionsWebserver;
import epmc.webserver.ProblemWebserver;

import static epmc.error.UtilError.ensure;

public class CommandTaskServer implements CommandTask {
    public final static String IDENTIFIER = "server";
    private static final String SERVER_WAITING_INCOMING = "serverWaitingIncoming";
    private Options options;

    @Override
    public String getIdentifier() {
        return IDENTIFIER;
    }

    @Override
    public void setModelChecker(ModelChecker modelChecker) {
    }

    @Override
    public boolean isRunOnServer() {
        return false;
    }
    
    @Override
    public void executeInClientBeforeServer() throws EPMCException {
    	options = Options.get();
    	ContextValue.set(new ContextValue());
        final int port = options.getInteger(OptionsWebserver.SERVER_PORT);
        final Registry registry = makeRegistry(port);
        try {
            String name = options.getString(OptionsWebserver.SERVER_NAME);
            EPMCRemote engine = new EPMCServer(name, port);
            registry.bind(name, engine);
        } catch (Exception e) {
        	System.out.println(e);
            ensure(false, ProblemWebserver.REMOTE);
        }

        CommandTask.super.executeInClientBeforeServer();
    }
    
    private static Registry makeRegistry(int port) throws EPMCException {
        try {
            return LocateRegistry.createRegistry(port);
        } catch (RemoteException e) {
            ensure(false, ProblemWebserver.CREATE_REGISTRY_FAILED, e, port);
            return null;
        }
    }
    
    private static void sendErrorAndExit(Problem problem, Object... parameters) {
        assert problem != null;
        assert parameters != null;
        for (Object parameter : parameters) {
            assert parameter != null;
        }
//        System.out.print(ISCASMCEXCEPTION_INDICATOR);
//        System.out.print(SPACE);
        System.out.print(problem.getResourceBundle());
//        System.out.print(SPACE);
        System.out.print(problem.getIdentifier());
        for (Object parameter : parameters) {
//            System.out.print(SPACE);
            System.out.print(parameter);
        }
        System.out.println();
        System.out.flush();
        System.exit(1);
    }
}
