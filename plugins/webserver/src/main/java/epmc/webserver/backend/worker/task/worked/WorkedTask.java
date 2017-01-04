package epmc.webserver.backend.worker.task.worked;

import epmc.webserver.backend.worker.task.Task;
import epmc.webserver.common.TaskOperation;

/**
 * A task representing a worked task, i.e., a task that has been finished
 * @author ori
 */
public abstract class WorkedTask extends Task {

	/**
	 * Create a new worked task identified by taskId for the user identified by userId
	 * @param userId the identifier of the user this task belongs to, as in the database
	 * @param taskId the identifier of this task, as in the database
	 * @param operation the operation to perform on this task, as extracted from the database
	 */
	protected WorkedTask(int userId, int taskId, TaskOperation operation) {
		super(userId, taskId, operation);
	}
}
