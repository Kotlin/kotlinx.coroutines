package kotlinx.coroutines.experimental

import java.util.concurrent.locks.LockSupport
import kotlin.coroutines.Continuation
import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.startCoroutine
import kotlin.coroutines.suspendCoroutine

// --------------- basic coroutine builders ---------------

/**
 * Launches new coroutine without blocking current thread and returns a reference to the coroutine as a [Job].
 * The [context] for the new coroutine must be explicitly specified and must include [CoroutineDispatcher] element.
 * See [CoroutineDispatcher] for the standard [context] implementations that are provided by `kotlinx.coroutines`.
 * The specified context is added to the context of the parent running coroutine (if any) inside which this function
 * is invoked. The [Job] of the resulting coroutine is a child of the job of the parent coroutine (if any).
 *
 * Uncaught exceptions in this coroutine cancel parent job in the context by default
 * (unless [CoroutineExceptionHandler] is explicitly specified), which means that when `launch` is used from another
 * coroutine, any uncaught exception leads to the cancellation of parent coroutine.
 *
 * See [newCoroutineContext] for a description of debugging facilities that are available for newly created coroutine.
 */
fun launch(context: CoroutineContext, block: suspend () -> Unit): Job =
    StandaloneCoroutine(newCoroutineContext(context)).also { block.startCoroutine(it) }

/**
 * Calls the specified suspending block with a given coroutine context, suspends until it completes, and returns
 * the result. It immediately applies dispatcher from the new context, shifting execution of the block into the
 * different thread inside the block, and back when it completes.
 * The specified [context] is merged onto the current coroutine context.
 */
public suspend fun <T> run(context: CoroutineContext, block: suspend () -> T): T =
    suspendCoroutine { cont ->
        block.startCoroutine(object : Continuation<T> by cont {
            override val context: CoroutineContext = cont.context + context
        })
    }

/**
 * Runs new coroutine and *blocks* current thread *interruptibly* until its completion.
 * This function should not be used from coroutine. It is designed to bridge regular code blocking code
 * to libraries that are written in suspending style.
 * The [context] for the new coroutine must be explicitly specified and must include [CoroutineDispatcher] element.
 * See [CoroutineDispatcher] for the standard [context] implementations that are provided by `kotlinx.coroutines`.
 * The specified context is added to the context of the parent running coroutine (if any) inside which this function
 * is invoked. The [Job] of the resulting coroutine is a child of the job of the parent coroutine (if any).
 *
 * If this blocked thread is interrupted (see [Thread.interrupt]), then the coroutine job is cancelled and
 * this `runBlocking` invocation throws [InterruptedException].
 *
 * See [newCoroutineContext] for a description of debugging facilities that are available for newly created coroutine.
 */
@Throws(InterruptedException::class)
public fun <T> runBlocking(context: CoroutineContext, block: suspend () -> T): T =
    BlockingCoroutine<T>(newCoroutineContext(context)).also { block.startCoroutine(it) }.joinBlocking()

// --------------- implementation ---------------

private class StandaloneCoroutine(
    val parentContext: CoroutineContext
) : AbstractCoroutine<Unit>(parentContext) {
    init { initParentJob(parentContext[Job]) }

    override fun afterCompletion(state: Any?) {
        // note the use of the parent context below!
        if (state is CompletedExceptionally) handleCoroutineException(parentContext, state.cancelReason)
    }
}

private class BlockingCoroutine<T>(parentContext: CoroutineContext) : AbstractCoroutine<T>(parentContext) {
    val blockedThread: Thread = Thread.currentThread()

    init { initParentJob(parentContext[Job])  }

    override fun afterCompletion(state: Any?) {
        LockSupport.unpark(blockedThread)
    }

    @Suppress("UNCHECKED_CAST")
    fun joinBlocking(): T {
        while (isActive) {
            if (Thread.interrupted()) throw InterruptedException().also { cancel(it) }
            LockSupport.park(this)
        }
        val state = getState()
        (state as? CompletedExceptionally)?.let { throw it.exception }
        return state as T
    }
}
