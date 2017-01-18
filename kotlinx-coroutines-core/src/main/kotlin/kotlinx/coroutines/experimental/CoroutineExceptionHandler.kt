package kotlinx.coroutines.experimental

import kotlin.coroutines.CoroutineContext


/**
 * Helper function for coroutine builder implementations to handle uncaught exception in coroutines.
 * It tries to handle uncaught exception in the following way:
 * * If there is [CoroutineExceptionHandler] in the context, then it is used.
 * * Otherwise, if there is a [Job] in the context, then [Job.cancel] is invoked and if it
 *   returns `true` (it was still active), then the exception is considered to be handled.
 * * Otherwise, if exception is [CancellationException] then it is ignored.
 * * Otherwise, current thread's [Thread.uncaughtExceptionHandler] is used.
 */
fun handleCoroutineException(context: CoroutineContext, exception: Throwable) {
    context[CoroutineExceptionHandler]?.let {
        it.handleException(context, exception)
        return
    }
    // quit if successfully pushed exception as cancellation cancelReason
    if (context[Job]?.cancel(exception) ?: false) return
    // ignore CancellationException (they are normal means to terminate a coroutine)
    if (exception is CancellationException) return
    // otherwise just use thread's handler
    val currentThread = Thread.currentThread()
    currentThread.uncaughtExceptionHandler.uncaughtException(currentThread, exception)
}

/**
 * An optional element on the coroutine context to handler uncaught exceptions.
 * See [handleCoroutineException].
 */
public interface CoroutineExceptionHandler : CoroutineContext.Element {
    companion object Key : CoroutineContext.Key<CoroutineExceptionHandler>
    public fun handleException(context: CoroutineContext, exception: Throwable)
}
