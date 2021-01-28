package epmc.webserver;

import epmc.error.Problem;
import epmc.error.UtilError;

public class ProblemWebserver {
	private final static String PROBLEM_WEBSERVER = "ProblemWebserver";
	
	public static final Problem EXECUTE_NO_COMMAND_GIVEN = newProblem("execute-no-command-given");
	public static final Problem CREATE_REGISTRY_FAILED = newProblem("create-registry-failed");
	public static final Problem REMOTE = newProblem("remote");
	public static final Problem EXECUTE_CHANNEL_MISSING = newProblem("execute-channel-missing");
	
	private static Problem newProblem(String name) {
        assert name != null;
        return UtilError.newProblem(PROBLEM_WEBSERVER, name);
    }
}
