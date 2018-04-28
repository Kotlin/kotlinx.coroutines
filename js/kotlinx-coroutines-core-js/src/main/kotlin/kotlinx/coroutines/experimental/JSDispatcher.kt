/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental

import kotlinx.coroutines.experimental.timeunit.TimeUnit
import kotlin.coroutines.experimental.*
import org.w3c.dom.*

internal class NodeDispatcher : CoroutineDispatcher(), Delay {
    override fun dispatch(context: CoroutineContext, block: Runnable) {
        setTimeout({ block.run() }, 0)
    }

    override fun scheduleResumeAfterDelay(time: Long, unit: TimeUnit, continuation: CancellableContinuation<Unit>) {
        val handle = setTimeout({ with(continuation) { resumeUndispatched(Unit) } }, time.toIntMillis(unit))
        // Actually on cancellation, but clearTimeout is idempotent
        continuation.invokeOnCancellation { clearTimeout(handle) }
    }

    override fun invokeOnTimeout(time: Long, unit: TimeUnit, block: Runnable): DisposableHandle {
        val handle = setTimeout({ block.run() }, time.toIntMillis(unit))
        return object : DisposableHandle {
            override fun dispose() {
                clearTimeout(handle)
            }
        }
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

    override fun scheduleResumeAfterDelay(time: Long, unit: TimeUnit, continuation: CancellableContinuation<Unit>) {
        window.setTimeout({ with(continuation) { resumeUndispatched(Unit) } }, time.toIntMillis(unit))
    }

    override fun invokeOnTimeout(time: Long, unit: TimeUnit, block: Runnable): DisposableHandle {
        val handle = window.setTimeout({ block.run() }, time.toIntMillis(unit))
        return object : DisposableHandle {
            override fun dispose() {
                window.clearTimeout(handle)
            }
        }
    }
}

internal abstract class MessageQueue : Queue<Runnable>() {
    val yieldEvery = 16 // yield to JS event loop after this many processed messages

    private var scheduled = false
    
    abstract fun schedule()

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
                val element = poll() ?: return@process
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

private fun Long.toIntMillis(unit: TimeUnit): Int =
    unit.toMillis(this).coerceIn(0L, Int.MAX_VALUE.toLong()).toInt()

internal open class Queue<T : Any> {
    private var queue = arrayOfNulls<Any?>(8)
    private var head = 0
    private var tail = 0

    val isEmpty get() = head == tail

    fun poll(): T? {
        if (isEmpty) return null
        val result = queue[head]!!
        queue[head] = null
        head = head.next()
        @Suppress("UNCHECKED_CAST")
        return result as T
    }

    tailrec fun add(element: T) {
        val newTail = tail.next()
        if (newTail == head) {
            resize()
            add(element) // retry with larger size
            return
        }
        queue[tail] = element
        tail = newTail
    }

    private fun resize() {
        var i = head
        var j = 0
        val a = arrayOfNulls<Any?>(queue.size * 2)
        while (i != tail) {
            a[j++] = queue[i]
            i = i.next()
        }
        queue = a
        head = 0
        tail = j
    }

    private fun Int.next(): Int {
        val j = this + 1
        return if (j == queue.size) 0 else j
    }
}

// We need to reference global setTimeout and clearTimeout so that it works on Node.JS as opposed to
// using them via "window" (which only works in browser)
private external fun setTimeout(handler: dynamic, timeout: Int = definedExternally): Int
private external fun clearTimeout(handle: Int = definedExternally)
