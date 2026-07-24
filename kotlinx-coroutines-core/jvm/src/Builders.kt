@file:JvmMultifileClass
@file:JvmName("BuildersKt")

package kotlinx.coroutines

import kotlin.coroutines.*

/**
 * The same as [runBlocking], but for consumption from Java.
 * From Kotlin's point of view, this function has the exact same signature as the regular [runBlocking].
 * This is done so that it can not be called from Kotlin, despite the fact that it is public.
 *
 * We do not expose this [runBlocking] in the documentation, because it is not supposed to be used from Kotlin.
 *
 * @suppress
 */
@Throws(InterruptedException::class)
@Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE")
@kotlin.internal.LowPriorityInOverloadResolution
public fun <T> runBlocking(
    context: CoroutineContext = EmptyCoroutineContext, block: suspend CoroutineScope.() -> T
): T = runBlocking(context, block)

@Throws(InterruptedException::class)
@Suppress("UNUSED_PARAMETER")
internal actual fun <T> runBlockingImpl(
    newContext: CoroutineContext, eventLoop: EventLoop?, block: suspend CoroutineScope.() -> T
): T {
    val coroutineContext = newContext.minusKey(ContinuationInterceptor) + Dispatchers.Default
    val coroutine = BlockingCoroutine<T>(
        coroutineContext,
        Thread.currentThread()
    )
    coroutine.start(CoroutineStart.DEFAULT, coroutine, block)
    return coroutine.joinBlocking()
}

private class BlockingCoroutine<T>(
    parentContext: CoroutineContext,
    private val blockedThread: Thread
) : AbstractCoroutine<T>(parentContext, true, true) {

    override val isScopedCoroutine: Boolean get() = true

    override fun afterCompletion(state: Any?) {
        // wake up blocked thread
        if (Thread.currentThread() != blockedThread)
            unpark(blockedThread)
    }

    @Suppress("UNCHECKED_CAST")
    fun joinBlocking(): T {
        registerTimeLoopThread()
        try {
            while (!isCompleted) {
                parkNanos(this, Long.MAX_VALUE)
                if (Thread.interrupted()) cancelCoroutine(InterruptedException())
            }
        } finally { // paranoia
            unregisterTimeLoopThread()
        }
        // now return result
        val state = this.state.unboxState()
        (state as? CompletedExceptionally)?.let { throw it.cause }
        return state as T
    }
}
