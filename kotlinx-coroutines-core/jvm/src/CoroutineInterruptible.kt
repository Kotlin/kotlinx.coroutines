/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.atomicfu.AtomicRef
import kotlinx.atomicfu.atomic
import kotlinx.atomicfu.loop
import kotlin.coroutines.CoroutineContext

/**
 * This is the [CoroutineInterruptController] implementation on JVM. See [CoroutineInterruptController] for detailed
 * description and examples.
 */
object CoroutineInterruptible :
        CoroutineInterruptController(), ThreadContextElement<CoroutineInterruptible.ThreadState?> {

    /**
     * Update the complete state of a coroutine on JVM.
     * Transforms [InterruptedException] into [CancellationException] for coroutines with this context element.
     */
    @InternalCoroutinesApi
    override fun updateCoroutineCompleteState(completeState: Any?): Any? =
            if (completeState is CompletedExceptionally && completeState.cause is InterruptedException)
                CompletedExceptionally(CancellationException())
            else
                completeState

    /**
     * Updates context of the current thread.
     * This function is invoked before the coroutine in the specified [context] is resumed in the current thread.
     * Prepares interruption for this execution, watching the [Job] for cancellation and interrupt this executing
     * thread on cancellation.
     */
    @InternalCoroutinesApi
    override fun updateThreadContext(context: CoroutineContext): ThreadState? {
        // Fast path: no Job in this context
        val job = context[Job] ?: return null
        // Slow path
        val threadState = ThreadState()
        threadState.initInterrupt(job)
        return threadState
    }

    /**
     * Restores context of the current thread.
     * This function is invoked after the coroutine in the specified [context] is suspended in the current thread.
     * Stops watching the [Job] for cancellation and do clean-up work.
     */
    @InternalCoroutinesApi
    override fun restoreThreadContext(context: CoroutineContext, oldState: ThreadState?) {
        // Fast path: no Job in this context
        val threadState = oldState ?: return
        // Slow path
        threadState.clearInterrupt()
    }

    /**
     * Holds the state of executions for interruption.
     */
    @InternalCoroutinesApi
    class ThreadState {
        fun initInterrupt(job: Job) {
            initInvokeOnCancel(job)
            initThread()
        }

        fun clearInterrupt() {
            state.loop { s ->
                when {
                    s is Working -> {
                        if (state.compareAndSet(s, Finish)) {
                            s.cancelHandle?.let { it.dispose() } // no more watching
                            return
                        }
                    }
                    s === Interrupting -> Thread.yield() // eases the thread
                    s === Interrupted -> { Thread.interrupted(); return } // no interrupt leak
                    s === Init || s === Finish -> throw IllegalStateException("impossible state")
                    else -> throw IllegalStateException("unknown state")
                }
            }
        }

        private fun initInvokeOnCancel(job: Job) {
            // watches the job for cancellation
            val cancelHandle =
                    job.invokeOnCompletion(onCancelling = true, invokeImmediately = true, handler = CancelHandler())
            // remembers the cancel handle or drops it
            state.loop { s ->
                when {
                    s === Init -> if (state.compareAndSet(s, Working(null, cancelHandle))) return
                    s is Working -> if (state.compareAndSet(s, Working(s.thread, cancelHandle))) return
                    s === Finish -> { cancelHandle.dispose(); return } // no more watching needed
                    s === Interrupting || s === Interrupted -> return
                    else -> throw IllegalStateException("unknown state")
                }
            }
        }

        private fun initThread() {
            val thread = Thread.currentThread()
            state.loop { s ->
                when {
                    s === Init -> if (state.compareAndSet(s, Working(thread, null))) return
                    s is Working -> if (state.compareAndSet(s, Working(thread, s.cancelHandle))) return
                    s === Interrupted -> { thread.interrupt(); return } // interrupted before the thread is set
                    s === Finish || s === Interrupting  -> throw IllegalStateException("impossible state")
                    else -> throw IllegalStateException("unknown state")
                }
            }
        }

        private inner class CancelHandler : CompletionHandler {
            override fun invoke(cause: Throwable?) {
                state.loop { s ->
                    when {
                        s === Init || (s is Working && s.thread === null) -> {
                            if (state.compareAndSet(s, Interrupted))
                                return
                        }
                        s is Working -> {
                            if (state.compareAndSet(s, Interrupting)) {
                                s.thread!!.interrupt()
                                state.value = Interrupted
                                return
                            }
                        }
                        s === Finish -> return
                        s === Interrupting || s === Interrupted -> return
                        else -> throw IllegalStateException("unknown state")
                    }
                }
            }
        }

        private val state: AtomicRef<State> = atomic(Init)

        private interface State
        // initial state
        private object Init : State
        // cancellation watching is setup and/or the continuation is running
        private data class Working(val thread: Thread?, val cancelHandle: DisposableHandle?) : State
        // the continuation done running without interruption
        private object Finish : State
        // interrupting this thread
        private object Interrupting: State
        // done interrupting
        private object Interrupted: State
    }
}
