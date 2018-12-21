/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import org.w3c.dom.*

private const val MAX_DELAY = Int.MAX_VALUE.toLong()

private fun delayToInt(timeMillis: Long): Int =
    timeMillis.coerceIn(0, MAX_DELAY).toInt()

internal class NodeDispatcher : CoroutineDispatcher(), Delay {
    override fun dispatch(context: CoroutineContext, block: Runnable) {
        setTimeout({ block.run() }, 0)
    }

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
    private val messageName = "dispatchCoroutine"

    private val queue = object : MessageQueue() {
        override fun schedule() {
            window.postMessage(messageName, "*")
        }
    }

    init {
        window.addEventListener("message", { event: dynamic ->
            if (event.source == window && event.data == messageName) {
                event.stopPropagation()
                queue.process()
            }
        }, true)
    }

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        queue.enqueue(block)
    }

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

internal abstract class MessageQueue : ArrayQueue<Runnable>() {
    val yieldEvery = 16 // yield to JS event loop after this many processed messages

    private var scheduled = false
    
    abstract fun schedule()

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
                schedule()
            }
        }
    }
}

// We need to reference global setTimeout and clearTimeout so that it works on Node.JS as opposed to
// using them via "window" (which only works in browser)
private external fun setTimeout(handler: dynamic, timeout: Int = definedExternally): Int
private external fun clearTimeout(handle: Int = definedExternally)
