/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlin.coroutines.*

/**
 * Calls the specified [block] with a given coroutine context in an interruptible manner.
 * The blocking code block will be interrupted and this function will throw [CancellationException]
 * if the coroutine is cancelled.
 *
 * Example:
 *
 * ```
 * withTimeout(500L) {            // Cancels coroutine on timeout
 *     runInterruptible {         // Throws CancellationException if interrupted
 *         doSomethingBlocking()  // Interrupted on coroutines cancellation
 *     }
 * }
 * ```
 *
 * There is an optional [context] parameter to this function working just like [withContext].
 * It enables single-call conversion of interruptible Java methods into suspending functions.
 * With one call here we are moving the call to [Dispatchers.IO] and supporting interruption:
 *
 * ```
 * suspend fun <T> BlockingQueue<T>.awaitTake(): T =
 *         runInterruptible(Dispatchers.IO) { queue.take() }
 * ```
 *
 * `runInterruptible` uses [withContext] as an underlying mechanism for switching context,
 * meaning that the supplied [block] is invoked in an [undispatched][CoroutineStart.UNDISPATCHED]
 * manner directly by the caller if [CoroutineDispatcher] from the current [coroutineContext][currentCoroutineContext]
 * is the same as the one supplied in [context].
 */
public suspend fun <T> runInterruptible(
    context: CoroutineContext = EmptyCoroutineContext,
    block: () -> T
): T = withContext(context) {
    runInterruptibleInExpectedContext(coroutineContext, block)
}

private fun <T> runInterruptibleInExpectedContext(coroutineContext: CoroutineContext, block: () -> T): T {
    try {
        val threadState = ThreadState(coroutineContext.job)
        threadState.setup()
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

private class ThreadState(private val job: Job) : CompletionHandler {
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
       |  INTERRUPTED  |                              |         FINISHED        |
       +---------------+                              +-------------------------+
    */
    private val _state = atomic(WORKING)
    private val targetThread = Thread.currentThread()

    // Registered cancellation handler
    private var cancelHandle: DisposableHandle? = null

    fun setup() {
        cancelHandle = job.invokeOnCompletion(onCancelling = true, invokeImmediately = true, handler = this)
        // Either we successfully stored it or it was immediately cancelled
        _state.loop { state ->
            when (state) {
                // Happy-path, move forward
                WORKING -> if (_state.compareAndSet(state, WORKING)) return
                // Immediately cancelled, just continue
                INTERRUPTING, INTERRUPTED -> return
                else -> invalidState(state)
            }
        }
    }

    fun clearInterrupt() {
        /*
         * Do not allow to untriggered interrupt to leak
         */
        _state.loop { state ->
            when (state) {
                WORKING -> if (_state.compareAndSet(state, FINISHED)) {
                    cancelHandle?.dispose()
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
                    Thread.interrupted()
                    return
                }
                else -> invalidState(state)
            }
        }
    }

    // Cancellation handler
    override fun invoke(cause: Throwable?) {
        _state.loop { state ->
            when (state) {
                // Working -> try to transite state and interrupt the thread
                WORKING -> {
                    if (_state.compareAndSet(state, INTERRUPTING)) {
                        targetThread.interrupt()
                        _state.value = INTERRUPTED
                        return
                    }
                }
                // Finished -- runInterruptible is already complete, INTERRUPTING - ignore
                FINISHED, INTERRUPTING, INTERRUPTED -> return
                else -> invalidState(state)
            }
        }
    }

    private fun invalidState(state: Int): Nothing = error("Illegal state $state")
}
