package epmc.webserver;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.rmi.RemoteException;
import java.rmi.server.UnicastRemoteObject;
import java.text.MessageFormat;
import java.util.Map;

import epmc.command.CommandTaskCheck;
import epmc.error.EPMCException;
import epmc.main.LogCommandLine;
import epmc.main.error.ProblemsEPMC;
import epmc.main.messages.MessagesEPMC;
import epmc.main.options.OptionsEPMC;
import epmc.messages.OptionsMessages;
import epmc.modelchecker.Model;
import epmc.modelchecker.ModelChecker;
import epmc.modelchecker.ModelDummy;
import epmc.modelchecker.Properties;
import epmc.modelchecker.RawModel;
import epmc.modelchecker.RawProperty;
import epmc.modelchecker.options.OptionsModelChecker;
import epmc.options.Options;
import epmc.options.UtilOptions;
import epmc.plugin.AfterCommandExecution;
import epmc.plugin.AfterModelCreation;
import epmc.plugin.BeforeModelCreation;
import epmc.plugin.UtilPlugin;
import epmc.util.Util;
import epmc.value.ContextValue;

import static epmc.error.UtilError.ensure;

public class EPMCServer extends UnicastRemoteObject implements EPMCRemote{

	private static final long serialVersionUID = 1L;
    final static String EXIT = "exit";
    private final static String SCM_REVISION = "SCM-Revision";

	public EPMCServer(String name, int port) throws RemoteException {
		super(port);
	}

	@Override
	public ModelCheckerResult execute(RawModel rawModel, EPMCMessageChannel channel, String serverName, String command, String inputType)
			throws RemoteException {
		System.out.println("execute in EPMCServer");
		
		Options options = Options.get();
		options.set(OptionsWebserver.SERVER_NAME, serverName);
		options.set(Options.COMMAND, command);
		options.set(OptionsModelChecker.MODEL_INPUT_TYPE, inputType);

		ContextValue.set(new ContextValue());
		ensure(channel != null, ProblemWebserver.EXECUTE_CHANNEL_MISSING);
        UtilPlugin.loadPlugins(options);
        
        LogCommandLine log = new LogCommandLine(options);
        options.set(OptionsMessages.LOG, log);
        
//        options.set(OptionsMessages.LOG, UtilMessages.newLog(channel));
//        System.out.println(options.get(OptionsMessages.LOG).getClass());
//        LogCommandLine log = options.get(OptionsMessages.LOG);
        String revision = Util.getManifestEntry(SCM_REVISION);
        if (revision != null) {
            revision = revision.trim();
        }
        if (revision != null && !revision.equals("")) {
            log.send(MessagesEPMC.RUNNING_EPMC_REVISION, revision);
        }
        OptionsTypesEPMC.RunMode runMode = options.get(OptionsWebserver.RUN_MODE);
        assert runMode != null;
        String commandName = options.getString(Options.COMMAND);
        
        System.out.println(commandName);
        ensure(commandName != null, ProblemWebserver.EXECUTE_NO_COMMAND_GIVEN);
        if (commandName.equals(EXIT)) {
            options.clear();
            UnicastRemoteObject.unexportObject(this, true);
            return null;
        }
        if (runMode == OptionsTypesEPMC.RunMode.COMMAND_LINE || runMode == OptionsTypesEPMC.RunMode.GUI) {
            boolean assertionsEnabled = false;
            try {
                assert false;
            } catch (AssertionError e) {
                assertionsEnabled = true;
            }
            if (assertionsEnabled) {
                log.send(MessagesEPMC.ASSERTIONS_ENABLED);
            } else {
                log.send(MessagesEPMC.ASSERTIONS_DISABLED);
            }
        }
        
        processBeforeModelLoadings(options);
        Model model = parseModel(rawModel);

//        System.out.println("-----*************-------- Options ------------");    
//        for (String key : options.getAllOptions().keySet())
//        {
//        	System.out.println(key + " : " + options.get(key));
//        }
//        System.out.println("------****************-------- Options end------------");

        System.out.println("parseModel Finished");
        System.out.println(model.getClass());
        processAfterModelLoadings(options);
        Properties properties = model.getPropertyList();

//        Map<String,Class<? extends CommandTask>> commands = options.get(OptionsEPMC.COMMAND_CLASS);
//        CommandTask command = Util.getInstance(commands, commandName);
        ModelChecker modelChecker = new ModelChecker(model);
//        command.setModelChecker(modelChecker);
        System.out.println("start to check");
        modelChecker.check();
        System.out.println("checking ends");
        
        ModelCheckerResult result = new ModelCheckerResult();
        int index = 0;
        for (RawProperty property : log.getProperties()) {
            String exprString = property.getName();
            if (exprString == null) {
                exprString = property.getDefinition();
            }
            Object propResult = log.get(property);
            if (propResult == null) {
                index++;
                continue;
            }
            String resultString = null;
            if (propResult instanceof EPMCException) {
                EPMCException e = (EPMCException) propResult;
                String message = e.getProblem().getMessage(options.getLocale());
                MessageFormat formatter = new MessageFormat(message);
                formatter.applyPattern(message);
                resultString = formatter.format(e.getArguments());
                if (options != null && options.getBoolean(OptionsEPMC.PRINT_STACKTRACE)) {
                    e.printStackTrace();
                }
            } else {
                resultString = propResult.toString();
            }
            System.out.println(exprString + "-------");
            System.out.println(resultString + "-------");
            result.add(property, resultString);
            index++;
        }

        
        
//        ModelCheckerResult result = command.executeInServer();
        processAfterCommandExecution(options);
//        
//        modelChecker.close();
//        context.close();
//        // remove options which cannot be serialized from options
//        options.removeOption(OptionsMessages.LOG);
//        options.removeOption(OptionsExpression.CONTEXT_EXPRESSION);
//        UtilRemote.removeClasses(options);
//        options.clear();
//        return result;
        return result;
	}

	@Override
	public String ttest() throws RemoteException{
		return "HHHHHH";
	}

	private void processBeforeModelLoadings(Options options) throws EPMCException {
		System.out.println( "(((()))))))))))))))))" );
        for (Class<? extends BeforeModelCreation> clazz : UtilPlugin.getPluginInterfaceClasses(Options.get(), BeforeModelCreation.class)) {
            BeforeModelCreation beforeModelLoading = null;
            beforeModelLoading = Util.getInstance(clazz);
            beforeModelLoading.process();
        }
    }

    private void processAfterModelLoadings(Options options) throws EPMCException {
    	System.out.println(UtilPlugin.getPluginInterfaceClasses(Options.get(), AfterModelCreation.class).size() + " -------------- ");
        for (Class<? extends AfterModelCreation> clazz : UtilPlugin.getPluginInterfaceClasses(Options.get(), AfterModelCreation.class)) {
        	
            AfterModelCreation afterModelLoading = null;
            afterModelLoading = Util.getInstance(clazz);
            afterModelLoading.process();
        }
    }

    private void processAfterCommandExecution(Options options) throws EPMCException {
        for (Class<? extends AfterCommandExecution> clazz : UtilPlugin.getPluginInterfaceClasses(Options.get(), AfterCommandExecution.class)) {
            AfterCommandExecution afterCommandExecution = null;
            afterCommandExecution = Util.getInstance(clazz);
            afterCommandExecution.process();
        }
    }
	private static Model parseModel(RawModel rawModel){
        Model model;
        if (rawModel == null || rawModel.getModelInputStreams().length == 0) {
            model = new ModelDummy();
        } else {
            InputStream[] inputs = rawModel.getModelInputStreams();
            model = UtilOptions.getInstance(OptionsModelChecker.MODEL_INPUT_TYPE);
            model.read(rawModel.getModelInputIdentifier(), inputs);

        }
        System.out.println("Parse Model Finished");
        
//        try {
//			System.out.println(new String(rawModel.getPropertyInputStreams()[0].readAllBytes()));
//		} catch (IOException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		}
        Properties properties = model.getPropertyList();
        if (rawModel != null
                && rawModel.getPropertyInputStreams() != null
                && rawModel.getPropertyInputStreams().length != 0
                && properties != null) {
            properties.parseProperties(rawModel.getPropertyInputIdentifier(), rawModel.getPropertyInputStreams());
        }
//        for(RawProperty p : properties.getRawProperties())
//        {
//        	System.out.println(p.getDefinition() + " **********");
//        }
        
        System.out.println("Parse Properties Finished");
        return model;
    }
}
