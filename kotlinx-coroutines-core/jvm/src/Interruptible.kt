/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.atomicfu.AtomicRef
import kotlinx.atomicfu.atomic
import kotlinx.atomicfu.loop
import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.EmptyCoroutineContext
import kotlin.coroutines.intrinsics.suspendCoroutineUninterceptedOrReturn

/**
 * Makes a blocking code block cancellable (become a cancellation point of the coroutine).
 *
 * The blocking code block will be interrupted and this function will throw [CancellationException]
 * if the coroutine is cancelled.
 *
 * Example:
 * ```
 * GlobalScope.launch(Dispatchers.IO) {
 *     async {
 *         // This function will throw [CancellationException].
 *         runInterruptible {
 *             doSomethingUseful()
 *
 *             // This blocking procedure will be interrupted when this coroutine is canceled
 *             // by Exception thrown by the below async block.
 *             doSomethingElseUsefulInterruptible()
 *         }
 *     }
 *
 *     async {
 *        delay(500L)
 *        throw Exception()
 *     }
 * }
 * ```
 *
 * There is also an optional context parameter to this function to enable single-call conversion of
 * interruptible Java methods into main-safe suspending functions like this:
 * ```
 * // With one call here we are moving the call to Dispatchers.IO and supporting interruption.
 * suspend fun <T> BlockingQueue<T>.awaitTake(): T =
 *         runInterruptible(Dispatchers.IO) { queue.take() }
 * ```
 *
 * @param context additional to [CoroutineScope.coroutineContext] context of the coroutine.
 * @param block regular blocking block that will be interrupted on coroutine cancellation.
 */
public suspend fun <T> runInterruptible(
        context: CoroutineContext = EmptyCoroutineContext,
        block: () -> T
): T = withContext(context) { runInterruptibleInExpectedContext(block) }

private suspend fun <T> runInterruptibleInExpectedContext(block: () -> T): T =
        suspendCoroutineUninterceptedOrReturn sc@{ uCont ->
            try {
                // fast path: no job
                val job = uCont.context[Job] ?: return@sc block()
                // slow path
                val threadState = ThreadState(job)
                try {
                    block()
                } finally {
                    threadState.clear()
                }
            } catch (e: InterruptedException) {
                throw CancellationException("runInterruptible: interrupted").initCause(e)
            }
        }

private const val WORKING      = 0
private const val FINISH       = 1
private const val INTERRUPTING = 2
private const val INTERRUPTED  = 3

private class ThreadState : CompletionHandler {
    /*
       === States ===

       WORKING: running normally
       FINISH: complete normally
       INTERRUPTING: canceled, going to interrupt this thread
       INTERRUPTED: this thread is interrupted


       === Possible Transitions ===

       +----------------+         remember           +-------------------------+
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
       |  INTERRUPTED  |                              |         FINISH          |
       +---------------+                              +-------------------------+
    */
    private val state: AtomicRef<State>

    private data class State(val state: Int, val thread: Thread? = null, val cancelHandle: DisposableHandle? = null)

    // We're using a non-primary constructor instead of init block of a primary constructor here, because
    // we need to `return`.
    constructor (job: Job) {
        state = atomic(State(WORKING, Thread.currentThread()))
        // watches the job for cancellation
        val cancelHandle =
                job.invokeOnCompletion(onCancelling = true, invokeImmediately = true, handler = this)
        // remembers the cancel handle or drops it
        state.loop { s ->
            when(s.state) {
                WORKING -> if (state.compareAndSet(s, State(WORKING, s.thread, cancelHandle))) return
                INTERRUPTING, INTERRUPTED -> return
                FINISH -> throw IllegalStateException("impossible state")
                else -> throw IllegalStateException("unknown state")
            }
        }
    }

    fun clear() {
        state.loop { s ->
            when(s.state) {
                WORKING -> if (state.compareAndSet(s, State(FINISH))) { s.cancelHandle!!.dispose(); return }
                INTERRUPTING -> { /* spin */ }
                INTERRUPTED -> { Thread.interrupted(); return } // no interrupt leak
                FINISH -> throw IllegalStateException("impossible state")
                else -> throw IllegalStateException("unknown state")
            }
        }
    }

    override fun invoke(cause: Throwable?) = onCancel(cause)

    private inline fun onCancel(cause: Throwable?) {
        state.loop { s ->
            when(s.state) {
                WORKING -> {
                    if (state.compareAndSet(s, State(INTERRUPTING))) {
                        s.thread!!.interrupt()
                        state.value = State(INTERRUPTED)
                        return
                    }
                }
                FINISH -> return
                INTERRUPTING, INTERRUPTED -> return
                else -> throw IllegalStateException("unknown state")
            }
        }
    }
}
