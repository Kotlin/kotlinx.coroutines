package kotlinx.coroutines.experimental

import kotlin.browser.window
import kotlin.coroutines.experimental.ContinuationInterceptor
import kotlin.coroutines.experimental.CoroutineContext

/**
 * A coroutine dispatcher that is not confined to any specific thread.
 * It executes initial continuation of the coroutine _right here_ in the current call-frame
 * and let the coroutine resume in whatever thread that is used by the corresponding suspending function, without
 * mandating any specific threading policy.
 *
 * Note, that if you need your coroutine to be confined to a particular thread or a thread-pool after resumption,
 * but still want to execute it in the current call-frame until its first suspension, then you can use
 * an optional [CoroutineStart] parameter in coroutine builders like [launch] and [async] setting it to the
 * the value of [CoroutineStart.UNDISPATCHED].
 */
public actual object Unconfined : CoroutineDispatcher() {
    actual override fun isDispatchNeeded(context: CoroutineContext): Boolean = false
    actual override fun dispatch(context: CoroutineContext, block: Runnable) { throw UnsupportedOperationException() }
    override fun toString(): String = "Unconfined"
}

/**
 * This is the default [CoroutineDispatcher] that is used by all standard builders like
 * [launch], [async], etc if no dispatcher nor any other [ContinuationInterceptor] is specified in their context.
 */
@Suppress("PropertyName")
public actual val DefaultDispatcher: CoroutineDispatcher = DefaultExecutor

internal object DefaultExecutor : CoroutineDispatcher(), Delay {
    fun enqueue(block: Runnable) {
        window.setTimeout({ block.run() }, 0)
    }

    fun schedule(time: Double, block: Runnable): Int =
        window.setTimeout({ block.run() }, time.timeToInt())

    fun removeScheduled(handle: Int) {
        window.clearTimeout(handle)
    }

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        window.setTimeout({ block.run() }, 0)
    }

    override fun scheduleResumeAfterDelay(time: Int, continuation: CancellableContinuation<Unit>) {
        window.setTimeout({ with(continuation) { resumeUndispatched(Unit) } }, time.coerceAtLeast(0))
    }

    override fun invokeOnTimeout(time: Int, block: Runnable): DisposableHandle {
        val handle = window.setTimeout({ block.run() }, time.coerceAtLeast(0))
        return object : DisposableHandle {
            override fun dispose() {
                window.clearTimeout(handle)
            }
        }
    }

    private fun Double.timeToInt(): Int = coerceIn(0.0..Int.MAX_VALUE.toDouble()).toInt()
}

/**
 * Creates context for the new coroutine. It installs [DefaultDispatcher] when no other dispatcher nor
 * [ContinuationInterceptor] is specified, and adds optional support for debugging facilities (when turned on).
 */
public fun newCoroutineContext(context: CoroutineContext, parent: Job? = null): CoroutineContext {
    val wp = if (parent == null) context else context + parent
    return if (context !== DefaultDispatcher && context[ContinuationInterceptor] == null)
        wp + DefaultDispatcher else wp
}
