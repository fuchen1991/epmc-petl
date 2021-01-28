package epmc.webserver;

import java.rmi.RemoteException;
import java.util.Date;
import java.util.concurrent.TimeUnit;

import epmc.error.EPMCException;
import epmc.error.UtilError;
import epmc.messages.Message;
import epmc.messages.OptionsMessages;
import epmc.messages.ProblemsMessages;
import epmc.options.Options;

public final class UtilMessages {
//    public static EPMCMessageChannel newMessageChannelCommandLine(Options options)
//            throws EPMCException {
//        assert options != null;
//        try {
//            return new EPMCMessageChannelCommandLine(options);
//        } catch (RemoteException e) {
//            UtilError.fail(ProblemsMessages.CREATE_COMMAND_LINE_MESSAGE_CHANNEL_FAILED, e.getMessage());
//            return null;
//        }
//    }
//    
//    public static EPMCMessageChannel newMessageChannelSilent(Options options)
//    throws EPMCException {
//        assert options != null;
//        try {
//            return new EPMCMessageChannelCommandLine(options);
//        } catch (RemoteException e) {
//            UtilError.fail(ProblemsMessages.CREATE_COMMAND_LINE_MESSAGE_CHANNEL_FAILED, e.getMessage());
//            return null;
//        }        
//    }
    
//    public static Log newLog(EPMCMessageChannel channel) throws EPMCException, RemoteException {
//        return new LogImpl(channel);
//    }
//
//    public static EPMCMessageChannel getChannel(Log log) {
//        return ((LogImpl) log).getChannel();
//    }
   
    public static String translateTimeStamp(Options options, long timeStarted, long time) {
        assert options != null;
        assert timeStarted >= 0;
        assert time >= 0;
        StringBuilder builder = new StringBuilder();
        OptionsTypesMessages.TimeStampFormat timeStampFormat = options.get(OptionsMessages.TIME_STAMPS);
        assert timeStampFormat != null;
        if (timeStampFormat != OptionsTypesMessages.TimeStampFormat.NONE) {
            builder.append("[");
        }
        switch (timeStampFormat) {
        case JAVA_DATE:
            builder.append(new Date(timeStarted + time));
            break;
        case MILLISECONDS_ABSOLUTE:
            builder.append(time + timeStarted);
            break;
        case MILLISECONDS_STARTED:
            builder.append(time);
            break;
        case NONE:
            break;
        case SECONDS_ABSOLUTE:
            builder.append(TimeUnit.MILLISECONDS.toSeconds(time + timeStarted));
            break;
        case SECONDS_STARTED:
            builder.append(TimeUnit.MILLISECONDS.toSeconds(time));
            break;
        default:
            break;
        }
        if (timeStampFormat != OptionsTypesMessages.TimeStampFormat.NONE) {
            builder.append("] ");
        }
        return builder.toString();
    }
    /**
     * Private constructor to avoid creation of objects of this class.
     */
    private UtilMessages() {
    }
}
