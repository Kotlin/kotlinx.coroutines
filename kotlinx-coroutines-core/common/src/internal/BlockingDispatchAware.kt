package kotlinx.coroutines.internal

/**
 * [Runnables][kotlinx.coroutines.Runnable] that are dispatched on [CoroutineDispatcher][kotlinx.coroutines.CoroutineDispatcher]
 * may optionally implement this interface to be notified of dispatch emulation in blocking mode.
 *
 * This may be needed for controlling dispatcher to release/acquire a permit of the worker that currently
 * executes the dispatched Runnable.
 * @see LimitedDispatcher.Worker
 * @see kotlinx.coroutines.scheduling.withUnlimitedIOScheduler
 */
internal interface BlockingDispatchAware {
    /**
     * Must not throw
     */
    fun beforeDispatchElsewhere()

    /**
     * Must not throw
     */
    fun afterDispatchBack()
}