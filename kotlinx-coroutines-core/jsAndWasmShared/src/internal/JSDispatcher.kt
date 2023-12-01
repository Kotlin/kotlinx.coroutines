/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

public expect abstract class W3CWindow
internal expect fun w3cSetTimeout(window: W3CWindow, handler: () -> Unit, timeout: Int): Int
internal expect fun w3cSetTimeout(handler: () -> Unit, timeout: Int): Int
internal expect fun w3cClearTimeout(handle: Int)
internal expect fun w3cClearTimeout(window: W3CWindow, handle: Int)

internal expect class ScheduledMessageQueue(dispatcher: SetTimeoutBasedDispatcher) : MessageQueue {
    override fun schedule()
    override fun reschedule()
    internal fun setTimeout(timeout: Int)
}

internal expect class WindowMessageQueue(window: W3CWindow) : MessageQueue {
    override fun schedule()
    override fun reschedule()
}

private const val MAX_DELAY = Int.MAX_VALUE.toLong()

private fun delayToInt(timeMillis: Long): Int =
    timeMillis.coerceIn(0, MAX_DELAY).toInt()

internal abstract class SetTimeoutBasedDispatcher: CoroutineDispatcher(), Delay {
    internal val messageQueue = ScheduledMessageQueue(this)

    abstract fun scheduleQueueProcessing()

    override fun limitedParallelism(parallelism: Int): CoroutineDispatcher {
        parallelism.checkParallelism()
        return this
    }

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        messageQueue.enqueue(block)
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle {
        val handle = w3cSetTimeout({ block.run() }, delayToInt(timeMillis))
        return ClearTimeout(handle)
    }

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        val handle = w3cSetTimeout({ with(continuation) { resumeUndispatched(Unit) } }, delayToInt(timeMillis))
        continuation.invokeOnCancellation(handler = ClearTimeout(handle).asHandler)
    }
}

internal class WindowDispatcher(private val window: W3CWindow) : CoroutineDispatcher(), Delay {
    private val queue = WindowMessageQueue(window)

    override fun dispatch(context: CoroutineContext, block: Runnable) = queue.enqueue(block)

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        val handle = w3cSetTimeout(window, { with(continuation) { resumeUndispatched(Unit) } }, delayToInt(timeMillis))
        continuation.invokeOnCancellation(handler = WindowClearTimeout(handle).asHandler)
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle {
        val handle = w3cSetTimeout(window, block::run, delayToInt(timeMillis))
        return WindowClearTimeout(handle)
    }

    private inner class WindowClearTimeout(handle: Int) : ClearTimeout(handle) {
        override fun dispose() {
            w3cClearTimeout(window, handle)
        }
    }
}

internal object SetTimeoutDispatcher : SetTimeoutBasedDispatcher() {
    override fun scheduleQueueProcessing() {
        messageQueue.setTimeout(0)
    }
}

private open class ClearTimeout(protected val handle: Int) : CancelHandler(), DisposableHandle {
    override fun dispose() {
        w3cClearTimeout(handle)
    }

    override fun invoke(cause: Throwable?) {
        dispose()
    }

    override fun toString(): String = "ClearTimeout[$handle]"
}


/**
 * An abstraction over JS scheduling mechanism that leverages micro-batching of dispatched blocks without
 * paying the cost of JS callbacks scheduling on every dispatch.
 *
 * Queue uses two scheduling mechanisms:
 * 1) [schedule] is used to schedule the initial processing of the message queue.
 *    JS engine-specific microtask mechanism is used in order to boost performance on short runs and a dispatch batch
 * 2) [reschedule] is used to schedule processing of the queue after yield to the JS event loop.
 *    JS engine-specific macrotask mechanism is used not to starve animations and non-coroutines macrotasks.
 *
 * Yet there could be a long tail of "slow" reschedules, but it should be amortized by the queue size.
 */
internal abstract class MessageQueue : MutableList<Runnable> by ArrayDeque() {
    val yieldEvery = 16 // yield to JS macrotask event loop after this many processed messages
    private var scheduled = false

    abstract fun schedule()

    abstract fun reschedule()

    fun enqueue(element: Runnable) {
        add(element)
        if (!scheduled) {
            scheduled = true
            schedule()
        }
    }

    fun process() {
        try {
            // limit number of processed messages
            repeat(yieldEvery) {
                val element = removeFirstOrNull() ?: return@process
                element.run()
            }
        } finally {
            if (isEmpty()) {
                scheduled = false
            } else {
                reschedule()
            }
        }
    }
}
