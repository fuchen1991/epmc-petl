package epmc.webserver;

import java.rmi.RemoteException;
import java.rmi.server.UnicastRemoteObject;
import java.text.MessageFormat;
import java.util.Locale;

import epmc.messages.Message;
import epmc.messages.MessageInstance;
import epmc.messages.OptionsMessages;
import epmc.options.Options;

public class EPMCMessageChannelCommandLine extends UnicastRemoteObject implements EPMCMessageChannel {
	private final boolean translate;
	private boolean started;
	private long timeStarted;
	private final Options options;
	private Class<ClassLoader> classLoaders;
	
	public EPMCMessageChannelCommandLine(Options options) throws RemoteException {
	    super();
	    assert options != null;
	    this.options = options;
	    this.translate = options.getBoolean(OptionsMessages.TRANSLATE_MESSAGES);
//	    if (options.getClass() == null) {
//	        this.classLoaders = new ArrayList<>();
//	    } else {
//	        this.classLoaders = options.getClass();
//	    }
	}
	
	private static final long serialVersionUID = 1L;
	private static MessageFormat formatter = new MessageFormat("");
	
	private String translateTimeStamp(long time) {
	    assert started;
	    assert time >= 0;
	    return UtilMessages.translateTimeStamp(options, timeStarted, time);
	}
	
	@Override
	public void setTimeStarted(long time) {
	    assert !started;
	    assert time >= 0;
	    timeStarted = time;
	    started = true;
	}
	
	@Override
	public void send(MessageInstance instance) {
	    assert started;
	    assert instance != null;
	    long time = instance.getTime();
	    Message message = instance.getMessage();
	    String[] parameters = instance.getParametersArray();
	    if (translate) {
	        System.out.print(translateTimeStamp(time));
	        Locale locale = this.options.getLocale();
	        formatter.applyPattern(message.getMessage(locale));
	        System.out.println(formatter.format(parameters));
	    } else {
	        System.out.print(message);
	        for (String argument : parameters) {
	            System.out.print(" " + argument);
	        }
	        System.out.println();
	    }
	}
}