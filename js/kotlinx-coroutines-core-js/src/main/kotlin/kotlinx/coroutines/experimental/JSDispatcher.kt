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

import kotlin.browser.*
import kotlin.coroutines.experimental.*

internal object JSDispatcher : CoroutineDispatcher(), Delay {
    // Check if we are in the browser and must use postMessage to avoid setTimeout throttling
    private val messageQueue =
        if (jsTypeOf(window) != "undefined") MessageQueue().apply { register() } else null

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        if (messageQueue != null) {
            messageQueue.enqueue(block)
        } else {
            setTimeout({ block.run() }, 0)
        }
    }

    override fun scheduleResumeAfterDelay(time: Int, continuation: CancellableContinuation<Unit>) {
        setTimeout({ with(continuation) { resumeUndispatched(Unit) } }, time.coerceAtLeast(0))
    }

    override fun invokeOnTimeout(time: Int, block: Runnable): DisposableHandle {
        val handle = setTimeout({ block.run() }, time.coerceAtLeast(0))
        return object : DisposableHandle {
            override fun dispose() {
                clearTimeout(handle)
            }
        }
    }
}

// it is open for tests
internal open class MessageQueue {
    val yieldEvery = 16 // yield to JS event loop after this many processed messages

    private val messageName = "JSDispatcher.dispatch"
    private var scheduled = false

    private var queue = arrayOfNulls<Runnable>(8)
    private var head = 0
    private var tail = 0

    fun register() {
        window.addEventListener("message", { event: dynamic ->
            if (event.source == window && event.data == messageName) {
                event.stopPropagation()
                process()
            }
        }, true)
    }

    // it is open for tests
    open fun schedule() {
        window.postMessage(messageName, "*")
    }

    val isEmpty get() = head == tail

    fun poll(): Runnable? {
        if (isEmpty) return null
        val result = queue[head]!!
        queue[head] = null
        head = head.next()
        return result
    }

    tailrec fun enqueue(block: Runnable) {
        val newTail = tail.next()
        if (newTail == head) {
            resize()
            enqueue(block) // retry with larger size
            return
        }
        queue[tail] = block
        tail = newTail
        if (!scheduled) {
            scheduled = true
            schedule()
        }
    }

    fun resize() {
        var i = head
        var j = 0
        val a = arrayOfNulls<Runnable>(queue.size * 2)
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

    fun process() {
        try {
            // limit number of processed messages
            repeat(yieldEvery) {
                val block = poll() ?: return@process
                block.run()
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
