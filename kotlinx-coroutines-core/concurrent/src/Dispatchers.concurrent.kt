package kotlinx.coroutines

/**
 * The [CoroutineDispatcher] that is designed for offloading blocking IO tasks to a shared pool of threads.
 * Additional threads in this pool are created on demand.
 * Default IO pool size is `64`; on JVM it can be configured using JVM-specific mechanisms,
 * please refer to `Dispatchers.IO` documentation on JVM platform.
 *
 * ### Elasticity for limited parallelism
 *
 * `Dispatchers.IO` has a unique property of elasticity: its views
 * obtained with [CoroutineDispatcher.limitedParallelism] are
 * not restricted by the `Dispatchers.IO` parallelism. Conceptually, there is
 * a dispatcher backed by an unlimited pool of threads, and both `Dispatchers.IO`
 * and views of `Dispatchers.IO` are actually views of that dispatcher. In practice
 * this means that, despite not abiding by `Dispatchers.IO`'s parallelism
 * restrictions, its views share threads and resources with it.
 *
 * In the following example
 * ```
 * // 100 threads for MySQL connection
 * val myMysqlDbDispatcher = Dispatchers.IO.limitedParallelism(100)
 * // 60 threads for MongoDB connection
 * val myMongoDbDispatcher = Dispatchers.IO.limitedParallelism(60)
 * ```
 * the system may have up to `64 + 100 + 60` threads dedicated to blocking tasks during peak loads,
 * but during its steady state there is only a small number of threads shared
 * among `Dispatchers.IO`, `myMysqlDbDispatcher` and `myMongoDbDispatcher`
 *
 * It is recommended to replace manually created thread-backed executors with `Dispatchers.IO.limitedParallelism` instead:
 * ```
 * // Requires manual closing, allocates resources for all threads
 * val databasePoolDispatcher = newFixedThreadPoolContext(128)
 *
 * // Provides the same number of threads as a resource but shares and caches them internally
 * val databasePoolDispatcher = Dispatchers.IO.limitedParallelism(128)
 * ```
 */
@Suppress("EXTENSION_SHADOWED_BY_MEMBER")
public expect val Dispatchers.IO: CoroutineDispatcher

internal actual fun rescheduleTaskFromClosedDispatcher(task: Runnable) {
    /**
     * We do not create a separate view of [Dispatchers.IO] for the cleanup needs.
     *
     * If [Dispatchers.IO] is not flooded with other tasks + the cleanup view does not have more threads than
     * [Dispatchers.IO], there is no difference between sending cleanup tasks to [Dispatchers.IO] and creating
     * a separate view of [Dispatchers.IO] for cleanup.
     *
     * If [Dispatchers.IO] is flooded with other tasks, we are at a crossroads:
     * - On the one hand, we do not want to create too many threads.
     *   Some clients are carefully monitoring the number of threads and are relying on it not being larger than
     *   the system property + the sum of explicit `limitedParallelism` arguments in the system.
     * - On the other hand, we don't want to delay productive tasks in favor of cleanup tasks.
     *
     * The first consideration wins on two accounts:
     * - As of writing this, [Dispatchers.IO] has been in use as the cleanup dispatcher for dispatchers obtained
     *   from JVM executors for years, and this has not caused any issues that we know of.
     * - On the other hand, some people likely rely on the number of threads not exceeding the number they control.
     *   If we were to create a separate view of [Dispatchers.IO] for cleanup, this number would be exceeded, which
     *   is a regression.
     */
    Dispatchers.IO.dispatch(Dispatchers.IO, task)
}
