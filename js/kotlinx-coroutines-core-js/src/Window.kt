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

import org.w3c.dom.Window

/**
 * Converts an instance of [Window] to an implementation of [CoroutineDispatcher].
 */
public fun Window.asCoroutineDispatcher(): CoroutineDispatcher =
    @Suppress("UnsafeCastFromDynamic")
    asDynamic().coroutineDispatcher ?: WindowDispatcher(this).also {
        asDynamic().coroutineDispatcher = it
    }

/**
 * Suspends coroutine until next JS animation frame and returns frame time on resumption.
 * The time is consistent with [window.performance.now()][org.w3c.performance.Performance.now].
 * This function is cancellable. If the [Job] of the current coroutine is completed while this suspending
 * function is waiting, this function immediately resumes with [CancellationException].
 */
public suspend fun Window.awaitAnimationFrame(): Double = suspendCancellableCoroutine { cont ->
    asWindowAnimationQueue().enqueue(cont)
}

private fun Window.asWindowAnimationQueue(): WindowAnimationQueue =
    @Suppress("UnsafeCastFromDynamic")
    asDynamic().coroutineAnimationQueue ?: WindowAnimationQueue(this).also {
        asDynamic().coroutineAnimationQueue = it
    }

private class WindowAnimationQueue(private val window: Window) {
    private val dispatcher = window.asCoroutineDispatcher()
    private var scheduled = false
    private var current = Queue<CancellableContinuation<Double>>()
    private var next = Queue<CancellableContinuation<Double>>()
    private var timestamp = 0.0

    fun enqueue(cont: CancellableContinuation<Double>) {
        next.add(cont)
        if (!scheduled) {
            scheduled = true
            window.requestAnimationFrame { ts ->
                timestamp = ts
                val prev = current
                current = next
                next = prev
                scheduled = false
                process()
            }
        }
    }

    fun process() {
        while(true) {
            val element = current.poll() ?: return
            with(element) { dispatcher.resumeUndispatched(timestamp) }
        }
    }
}