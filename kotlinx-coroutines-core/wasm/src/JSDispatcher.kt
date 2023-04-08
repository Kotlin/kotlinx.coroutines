/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import org.w3c.dom.*
import kotlin.coroutines.*
import kotlin.js.*

private const val MAX_DELAY = Int.MAX_VALUE.toLong()

private fun delayToInt(timeMillis: Long): Int =
    timeMillis.coerceIn(0, MAX_DELAY).toInt()

internal sealed class SetTimeoutBasedDispatcher: CoroutineDispatcher(), Delay {
    inner class ScheduledMessageQueue : MessageQueue() {
        internal val processQueue: () -> Unit = ::process

        override fun schedule() {
            scheduleQueueProcessing()
        }

        override fun reschedule() {
            setTimeout(processQueue, 0)
        }
    }

    internal val messageQueue = ScheduledMessageQueue()

    abstract fun scheduleQueueProcessing()

    override fun limitedParallelism(parallelism: Int): CoroutineDispatcher {
        parallelism.checkParallelism()
        return this
    }

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        messageQueue.enqueue(block)
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle {
        val handle = setTimeout({ block.run() }, delayToInt(timeMillis))
        return ClearTimeout(handle)
    }

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        val handle = setTimeout({ with(continuation) { resumeUndispatched(Unit) } }, delayToInt(timeMillis))
        // Actually on cancellation, but clearTimeout is idempotent
        continuation.invokeOnCancellation(handler = ClearTimeout(handle).asHandler)
    }
}

internal class NodeDispatcher(private val process: JsProcess) : SetTimeoutBasedDispatcher() {
    override fun scheduleQueueProcessing() {
        process.nextTick(messageQueue.processQueue)
    }
}

internal object SetTimeoutDispatcher : SetTimeoutBasedDispatcher() {
    override fun scheduleQueueProcessing() {
        setTimeout(messageQueue.processQueue, 0)
    }
}

private open class ClearTimeout(protected val handle: Int) : CancelHandler(), DisposableHandle {

    override fun dispose() {
        clearTimeout(handle)
    }

    override fun invoke(cause: Throwable?) {
        dispose()
    }

    override fun toString(): String = "ClearTimeout[$handle]"
}

@Suppress("UNUSED_PARAMETER")
private fun toJsAnyCallback(handle: () -> Unit): JsAny = js("handle")

internal class WindowDispatcher(private val window: Window) : CoroutineDispatcher(), Delay {
    private val queue = WindowMessageQueue(window)

    override fun dispatch(context: CoroutineContext, block: Runnable) = queue.enqueue(block)

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        val handle = window.setTimeout(toJsAnyCallback { with(continuation) { resumeUndispatched(Unit) } }, delayToInt(timeMillis))
        continuation.invokeOnCancellation(handler = WindowClearTimeout(handle).asHandler)
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle {
        val handle = window.setTimeout(toJsAnyCallback(block::run), delayToInt(timeMillis))
        return WindowClearTimeout(handle)
    }

    private inner class WindowClearTimeout(handle: Int) : ClearTimeout(handle) {
        override fun dispose() {
            window.clearTimeout(handle)
        }
    }
}

@Suppress("UNUSED_PARAMETER")
private fun subscribeToWindowMessages(window: Window, process: () -> Unit): Unit = js("""{
    const handler = (event) => {
        if (event.source == window && event.data == 'dispatchCoroutine') {
            event.stopPropagation();
            process();
        }
    }
    window.addEventListener('message', handler, true);
}""")

@Suppress("UNUSED_PARAMETER")
private fun createRescheduleMessagePoster(window: Window): () -> Unit =
    js("() => window.postMessage('dispatchCoroutine', '*')")

@Suppress("UNUSED_PARAMETER")
private fun createScheduleMessagePoster(process: () -> Unit): () -> Unit =
    js("() => Promise.resolve(0).then(process)")

private class WindowMessageQueue(window: Window) : MessageQueue() {
    private val scheduleMessagePoster = createScheduleMessagePoster(::process)
    private val rescheduleMessagePoster = createRescheduleMessagePoster(window)
    init {
        subscribeToWindowMessages(window, ::process)
    }

    override fun schedule() {
        scheduleMessagePoster()
    }

    override fun reschedule() {
        rescheduleMessagePoster()
    }
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

// We need to reference global setTimeout and clearTimeout so that it works on Node.JS as opposed to
// using them via "window" (which only works in browser)
private external fun setTimeout(handler: () -> Unit, timeout: Int): Int

// d8 doesn't have clearTimeout
@Suppress("UNUSED_PARAMETER")
private fun clearTimeout(handle: Int): Unit =
    js("{ if (typeof clearTimeout !== 'undefined') clearTimeout(handle); }")
