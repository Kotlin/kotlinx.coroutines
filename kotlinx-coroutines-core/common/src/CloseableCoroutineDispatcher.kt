package kotlinx.coroutines

/**
 * [CoroutineDispatcher] that provides a method to close it,
 * causing the rejection of any new tasks and cleanup of all underlying resources
 * associated with the current dispatcher.
 * Examples of closeable dispatchers are dispatchers backed by `java.lang.Executor` and
 * by `kotlin.native.Worker`.
 *
 * **The `CloseableCoroutineDispatcher` class is not stable for inheritance in 3rd party libraries**, as new methods
 * might be added to this interface in the future, but is stable for use.
 */
@ExperimentalCoroutinesApi
public expect abstract class CloseableCoroutineDispatcher() : CoroutineDispatcher, AutoCloseable {

    /**
     * Initiate the closing sequence of the coroutine dispatcher.
     * After a successful call to [close], no new tasks will be accepted to be [dispatched][dispatch].
     * The previously-submitted tasks will still be run, but [close] is not guaranteed to wait for them to finish.
     *
     * Invocations of `close` are idempotent and thread-safe.
     */
    public abstract override fun close()
}
