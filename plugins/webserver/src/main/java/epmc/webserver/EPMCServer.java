package epmc.webserver;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.rmi.RemoteException;
import java.rmi.server.UnicastRemoteObject;
import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

//import epmc.command.CommandTaskCheck;
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
import epmc.prism.options.OptionsPRISM;
import epmc.propertysolver.OptionsUCT;
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
	public ModelCheckerResult execute(RawModel rawModel, EPMCMessageChannel channel, String petlSolver, Options opt)
			throws RemoteException {
		Options options = Options.get();
//		options.set(OptionsWebserver.SERVER_NAME, serverName);
//		options.set(Options.COMMAND, command);
//		options.set(OptionsModelChecker.MODEL_INPUT_TYPE, inputType);
		
		options.set(OptionsWebserver.SERVER_NAME, opt.getUnparsed(OptionsWebserver.SERVER_NAME));
		options.set(Options.COMMAND, opt.getUnparsed(Options.COMMAND));
		String inputType = opt.getUnparsed(OptionsModelChecker.MODEL_INPUT_TYPE);
		options.set(OptionsModelChecker.MODEL_INPUT_TYPE, inputType);
		if(inputType.equals("mas"))
		{
			options.set(OptionsPRISM.PRISM_FLATTEN, false);
			options.set(OptionsModelChecker.PROPERTY_INPUT_TYPE, "petl");
			options.set(OptionsUCT.BVALUE, opt.getUnparsed(OptionsUCT.BVALUE));
			options.set(OptionsUCT.RANDOM_SEED, opt.getUnparsed(OptionsUCT.RANDOM_SEED));
			options.set(OptionsUCT.UCT_DEPTH_LIMIT, opt.getUnparsed(OptionsUCT.UCT_DEPTH_LIMIT));
			options.set(OptionsUCT.UCT_TIME_LIMIT, opt.getUnparsed(OptionsUCT.UCT_TIME_LIMIT));
			List<String> ops = new ArrayList<String>();
			ops.add("z3");
			ops.add("-smt2");
			ops.add("{0}");
			if(petlSolver.equals("minlp"))
				options.set(OptionsModelChecker.PROPERTY_SOLVER, "propositional-explicit,operator-explicit,pctl-explicit-next,petl-explicit-knowledge,petl-until-minlp");
			else
				options.set(OptionsModelChecker.PROPERTY_SOLVER, "propositional-explicit,operator-explicit,pctl-explicit-next,petl-explicit-knowledge,petl-until-uct");
			options.set("constraintsolver-solver", "smt-lib-petl");
			options.set("smtlib-command-line", ops);
			options.set("smtlib-version", "v25");
		}

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

        processAfterModelLoadings(options);
        Properties properties = model.getPropertyList();

//        Map<String,Class<? extends CommandTask>> commands = options.get(OptionsEPMC.COMMAND_CLASS);
//        CommandTask command = Util.getInstance(commands, commandName);
        ModelChecker modelChecker = new ModelChecker(model);
//        command.setModelChecker(modelChecker);
        modelChecker.check();
        
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
            result.add(property, resultString);
            index++;
        }
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

	private void processBeforeModelLoadings(Options options) throws EPMCException {
        for (Class<? extends BeforeModelCreation> clazz : UtilPlugin.getPluginInterfaceClasses(Options.get(), BeforeModelCreation.class)) {
            BeforeModelCreation beforeModelLoading = null;
            beforeModelLoading = Util.getInstance(clazz);
            beforeModelLoading.process();
        }
    }

    private void processAfterModelLoadings(Options options) throws EPMCException {
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
        Properties properties = model.getPropertyList();
        if (rawModel != null
                && rawModel.getPropertyInputStreams() != null
                && rawModel.getPropertyInputStreams().length != 0
                && properties != null) {
            properties.parseProperties(rawModel.getPropertyInputIdentifier(), rawModel.getPropertyInputStreams());
        }
        
        return model;
    }
}
