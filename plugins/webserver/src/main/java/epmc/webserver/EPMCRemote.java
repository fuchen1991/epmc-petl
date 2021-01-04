package epmc.webserver;

import java.rmi.Remote;
import java.rmi.RemoteException;

import epmc.modelchecker.RawModel;
import epmc.options.Options;
import epmc.webserver.backend.worker.channel.PrismModelMessageChannel;

public interface EPMCRemote extends Remote {
	/**
     * Execute task on IscasMC server.
     * 
     * @param model unparsed model to check
     * @param options options used
     * @param channel channel to send information back to client
     * @return result of model checking process
     * @throws RemoteException thrown in case of connection problems
     */
//    public ModelCheckerResult execute
//    (RawModel model, Options options, EPMCMessageChannel channel)
//            throws RemoteException;
    
    public ModelCheckerResult execute
    (RawModel model, EPMCMessageChannel channel, String serverName, String command, String inputType)
            throws RemoteException;
    
    public String ttest() throws RemoteException;
}
