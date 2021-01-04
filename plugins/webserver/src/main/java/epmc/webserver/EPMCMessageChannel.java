package epmc.webserver;

import java.rmi.Remote;
import java.rmi.RemoteException;

import epmc.messages.MessageInstance;

public interface EPMCMessageChannel extends Remote{
	void setTimeStarted(long time) throws RemoteException;

    void send(MessageInstance instance) throws RemoteException;
}
