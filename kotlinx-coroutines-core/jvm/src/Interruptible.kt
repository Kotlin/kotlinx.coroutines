/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlin.coroutines.*

/**
 * Calls the specified [block] with a given coroutine context in a interruptible manner.
 * The blocking code block will be interrupted and this function will throw [CancellationException]
 * if the coroutine is cancelled.
 * The specified [coroutineContext] directly translates into [withContext] argument.
 *
 * Example:
 * ```
 * val blockingJob = launch {
 *     // This function will throw CancellationException
 *     runInterruptible(Dispatchers.IO) {
 *         // This blocking procedure will be interrupted when this coroutine is canceled
 *         doSomethingElseUsefulInterruptible()
 *     }
 * }
 *
 *     delay(500L)
 *     blockingJob.cancel() // Interrupt blocking call
 * }
 * ```
 *
 * There is also an optional context parameter to this function to enable single-call conversion of
 * interruptible Java methods into suspending functions like this:
 * ```
 * // With one call here we are moving the call to Dispatchers.IO and supporting interruption.
 * suspend fun <T> BlockingQueue<T>.awaitTake(): T =
 *         runInterruptible(Dispatchers.IO) { queue.take() }
 * ```
 */
public suspend fun <T> runInterruptible(
    context: CoroutineContext = EmptyCoroutineContext,
    block: () -> T
): T = withContext(context) {
    runInterruptibleInExpectedContext(block)
}

private suspend fun <T> runInterruptibleInExpectedContext(block: () -> T): T {
    try {
        // No job -> no cancellation
        val job = coroutineContext[Job] ?: return block()
        val threadState = ThreadState(job)
        try {
            return block()
        } finally {
            threadState.clearInterrupt()
        }
    } catch (e: InterruptedException) {
        throw CancellationException("Blocking call was interrupted due to parent cancellation").initCause(e)
    }
}

private const val WORKING = 0
private const val FINISHED = 1
private const val INTERRUPTING = 2
private const val INTERRUPTED = 3

private class ThreadState : CompletionHandler {
    /*
       === States ===

       WORKING: running normally
       FINISH: complete normally
       INTERRUPTING: canceled, going to interrupt this thread
       INTERRUPTED: this thread is interrupted

       === Possible Transitions ===

       +----------------+         register job       +-------------------------+
       |    WORKING     |   cancellation listener    |         WORKING         |
       | (thread, null) | -------------------------> | (thread, cancel handle) |
       +----------------+                            +-------------------------+
               |                                                |   |
               | cancel                                  cancel |   | complete
               |                                                |   |
               V                                                |   |
       +---------------+                                        |   |
       | INTERRUPTING  | <--------------------------------------+   |
       +---------------+                                            |
               |                                                    |
               | interrupt                                          |
               |                                                    |
               V                                                    V
       +---------------+                              +-------------------------+
       |  INTERRUPTED  |                              |         FINISHED         |
       +---------------+                              +-------------------------+
    */
    private val state: AtomicRef<State> = atomic(State(WORKING, null))
    private val targetThread = Thread.currentThread()

    private data class State(@JvmField val state: Int, @JvmField val cancelHandle: DisposableHandle?)

    // We're using a non-primary constructor instead of init block of a primary constructor here, because
    // we need to `return`.
    constructor(job: Job) {
        // Register cancellation handler
        val cancelHandle =
            job.invokeOnCompletion(onCancelling = true, invokeImmediately = true, handler = this)
        // Either we successfully stored it or it was immediately cancelled
        state.loop { s ->
            when (s.state) {
                // Happy-path, move forward
                WORKING -> if (state.compareAndSet(s, State(WORKING, cancelHandle))) return
                // Immediately cancelled, just continue
                INTERRUPTING, INTERRUPTED -> return
                else -> throw IllegalStateException("Illegal state $s")
            }
        }
    }

    fun clearInterrupt() {
        /*
         * Do not allow to untriggered interrupt to leak
         */
        state.loop { s ->
            when (s.state) {
                WORKING -> if (state.compareAndSet(s, State(FINISHED, null))) {
                    s.cancelHandle?.dispose()
                    return
                }
                INTERRUPTING -> {
                   /*
                    * Spin, cancellation mechanism is interrupting our thread right now
                    * and we have to wait it and then clear interrupt status
                    */
                }
                INTERRUPTED -> {
                    // Clear it and bail out
                    Thread.interrupted();
                    return
                }
                else -> error("Illegal state: $s")
            }
        }
    }

    // Cancellation handler
    override fun invoke(cause: Throwable?) {
        state.loop { s ->
            when (s.state) {
                // Working -> try to transite state and interrupt the thread
                WORKING -> {
                    if (state.compareAndSet(s, State(INTERRUPTING, null))) {
                        targetThread.interrupt()
                        state.value = State(INTERRUPTED, null)
                        return
                    }
                }
                // Finished -- runInterruptible is already complete
                FINISHED -> return
                INTERRUPTING, INTERRUPTED -> return
                else -> error("Illegal state: $s")
            }
        }
    }
}
