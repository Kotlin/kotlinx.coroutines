package kotlinx.coroutines.experimental.io.internal

import kotlinx.atomicfu.*
import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*
import kotlin.coroutines.experimental.intrinsics.*

/**
 * Semi-cancellable reusable continuation. Unlike regular continuation this implementation has limitations:
 * - could be resumed only once per swap, undefined behaviour otherwise
 * - [T] should be neither [Throwable] nor [Continuation]
 * - value shouldn't be null
 */
internal class MutableDelegateContinuation<T : Any> : Continuation<T>, DispatchedTask<T> {
    private var _delegate: Continuation<T>? = null
    private val state = atomic<Any?>(null)
    private val handler = atomic<JobRelation?>(null)

    override val delegate: Continuation<T>
        get() = _delegate!!

    override fun takeState(): Any? {
        val value = state.getAndSet(null)
        _delegate = null
        return value
    }

    fun swap(actual: Continuation<T>): Any {
        loop@while (true) {
            val before = state.value

            when (before) {
                null -> {
                    if (!state.compareAndSet(null, actual)) continue@loop
                    parent(actual.context)
                    return COROUTINE_SUSPENDED
                }
                else -> {
                    if (!state.compareAndSet(before, null)) continue@loop
                    if (before is Throwable) throw before
                    @Suppress("UNCHECKED_CAST")
                    return before as T
                }
            }
        }
    }

    fun close() {
        resumeWithException(Cancellation)
        handler.getAndSet(null)?.dispose()
    }

    private fun parent(context: CoroutineContext) {
        val job = context[Job]
        if (handler.value?.job === job) return

        if (job == null) {
            handler.getAndSet(null)?.dispose()
        } else {
            val handler = JobRelation(job)
            val old = this.handler.getAndUpdate { j ->
                when {
                    j == null -> handler
                    j.job === job -> return
                    else -> handler
                }
            }
            old?.dispose()
        }
    }

    override val context: CoroutineContext
        get() = (state.value as? Continuation<*>)?.context ?: EmptyCoroutineContext

    override fun resume(value: T) {
        loop@while(true) {
            val before = state.value

            when (before) {
                null -> {
                    if (!state.compareAndSet(null, value)) continue@loop
                    return
                }
                is Continuation<*> -> {
                    if (!state.compareAndSet(before, value)) continue@loop
                    @Suppress("UNCHECKED_CAST")
                    val cont = before as Continuation<T>
                    _delegate = cont
                    return dispatch(1)
                }
                else -> return
            }
        }
    }

    override fun resumeWithException(exception: Throwable) {
        loop@while(true) {
            val before = state.value

            when (before) {
                null -> {
                    if (!state.compareAndSet(null, exception)) continue@loop
                    return
                }
                is Continuation<*> -> {
                    if (!state.compareAndSet(before, CompletedExceptionally(exception))) continue@loop
                    @Suppress("UNCHECKED_CAST")
                    val cont = before as Continuation<T>
                    _delegate = cont
                    return dispatch(1)
                }
                else -> return
            }
        }
    }

    private fun resumeWithExceptionContinuationOnly(job: Job, exception: Throwable) {
        var c: Continuation<*>? = null

        state.update {
            if (it !is Continuation<*>) return
            if (it.context[Job] !== job) return
            c = it
            null
        }

        c!!.resumeWithException(exception)
    }

    private inner class JobRelation(val job: Job) : CompletionHandler, DisposableHandle {
        private var handler: DisposableHandle = NonDisposableHandle

        init {
            val h = job.invokeOnCompletion(onCancelling = true, handler = this)
            if (job.isActive) {
                handler = h
            }
        }

        override fun invoke(cause: Throwable?) {
            this@MutableDelegateContinuation.handler.compareAndSet(this, null)
            dispose()

            if (cause != null) {
                resumeWithExceptionContinuationOnly(job, cause)
            }
        }

        override fun dispose() {
            handler.dispose()
            handler = NonDisposableHandle
        }
    }

    private companion object {
        val Cancellation = CancellationException("Continuation terminated")
    }
}