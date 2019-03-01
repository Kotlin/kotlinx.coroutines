/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import org.w3c.dom.*
import kotlin.coroutines.*
import kotlin.js.*

private const val MAX_DELAY = Int.MAX_VALUE.toLong()

private fun delayToInt(timeMillis: Long): Int =
    timeMillis.coerceIn(0, MAX_DELAY).toInt()

internal object NodeDispatcher : CoroutineDispatcher(), Delay {
    override fun dispatch(context: CoroutineContext, block: Runnable) = NodeJsMessageQueue.enqueue(block)

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        val handle = setTimeout({ with(continuation) { resumeUndispatched(Unit) } }, delayToInt(timeMillis))
        // Actually on cancellation, but clearTimeout is idempotent
        continuation.invokeOnCancellation(handler = ClearTimeout(handle).asHandler)
    }

    private class ClearTimeout(private val handle: Int) : CancelHandler(), DisposableHandle {
        override fun dispose() { clearTimeout(handle) }
        override fun invoke(cause: Throwable?) { dispose() }
        override fun toString(): String = "ClearTimeout[$handle]"
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable): DisposableHandle {
        val handle = setTimeout({ block.run() }, delayToInt(timeMillis))
        return ClearTimeout(handle)
    }
}

internal class WindowDispatcher(private val window: Window) : CoroutineDispatcher(), Delay {
    private val queue = WindowMessageQueue(window)

    override fun dispatch(context: CoroutineContext, block: Runnable) = queue.enqueue(block)

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        window.setTimeout({ with(continuation) { resumeUndispatched(Unit) } }, delayToInt(timeMillis))
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable): DisposableHandle {
        val handle = window.setTimeout({ block.run() }, delayToInt(timeMillis))
        return object : DisposableHandle {
            override fun dispose() {
                window.clearTimeout(handle)
            }
        }
    }
}

private class WindowMessageQueue(private val window: Window) : MessageQueue() {
    private val messageName = "dispatchCoroutine"

    init {
        window.addEventListener("message", { event: dynamic ->
            if (event.source == window && event.data == messageName) {
                event.stopPropagation()
                process()
            }
        }, true)
    }

    override fun schedule() {
        Promise.resolve(Unit).then({ process() })
    }

    override fun reschedule() {
        window.postMessage(messageName, "*")
    }
}

private object NodeJsMessageQueue : MessageQueue() {
    override fun schedule() {
        // next tick is even faster than resolve
        process.nextTick({ process() })
    }

    override fun reschedule() {
        setTimeout({ process() }, 0)
    }
}

/**
 * An abstraction over JS scheduling mechanism that leverages micro-batching of [dispatch] blocks without
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
internal abstract class MessageQueue : ArrayQueue<Runnable>() {
    val yieldEvery = 16 // yield to JS macrotask event loop after this many processed messages

    private var scheduled = false
    
    abstract fun schedule()

    abstract fun reschedule()

    fun enqueue(element: Runnable) {
        addLast(element)
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
            if (isEmpty) {
                scheduled = false
            } else {
                reschedule()
            }
        }
    }
}

// We need to reference global setTimeout and clearTimeout so that it works on Node.JS as opposed to
// using them via "window" (which only works in browser)
private external fun setTimeout(handler: dynamic, timeout: Int = definedExternally): Int
private external fun clearTimeout(handle: Int = definedExternally)
private external val process: dynamic
