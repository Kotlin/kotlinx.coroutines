package kotlinx.coroutines.scheduling

private val parallelismCompensationEnabled: Boolean =
    System.getProperty("kotlinx.coroutines.parallelism.compensation", "true").toBoolean()

/**
 * Introduced as part of IntelliJ patches.
 *
 * Increases the parallelism limit of the coroutine dispatcher associated with the current thread for the duration of [body] execution.
 * After the [body] completes, the effective parallelism may stay higher than the associated limit, but it is said
 * that eventually it will adjust to meet it.
 */
internal fun <T> withCompensatedParallelism(body: () -> T): T {
    if (!parallelismCompensationEnabled) {
        return body()
    }
    // CoroutineScheduler.Worker implements ParallelismCompensation
    val worker = Thread.currentThread() as? ParallelismCompensation
        ?: return body()
    worker.increaseParallelismAndLimit()
    try {
        return body()
    } finally {
        worker.decreaseParallelismLimit()
    }
}