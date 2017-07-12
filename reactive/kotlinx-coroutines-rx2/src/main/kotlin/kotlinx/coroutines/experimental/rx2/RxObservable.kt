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

package kotlinx.coroutines.experimental.rx2

import io.reactivex.Observable
import io.reactivex.ObservableEmitter
import io.reactivex.functions.Cancellable
import kotlinx.coroutines.experimental.AbstractCoroutine
import kotlinx.coroutines.experimental.Job
import kotlinx.coroutines.experimental.channels.ClosedSendChannelException
import kotlinx.coroutines.experimental.channels.ProducerScope
import kotlinx.coroutines.experimental.channels.SendChannel
import kotlinx.coroutines.experimental.handleCoroutineException
import kotlinx.coroutines.experimental.newCoroutineContext
import kotlinx.coroutines.experimental.selects.SelectInstance
import kotlinx.coroutines.experimental.sync.Mutex
import java.util.concurrent.atomic.AtomicIntegerFieldUpdater
import kotlin.coroutines.experimental.CoroutineContext
import kotlin.coroutines.experimental.startCoroutine

/**
 * Creates cold [observable][Observable] that will run a given [block] in a coroutine.
 * Every time the returned observable is subscribed, it starts a new coroutine in the specified [context].
 * Coroutine emits items with `send`. Unsubscribing cancels running coroutine.
 *
 * Invocations of `send` are suspended appropriately to ensure that `onNext` is not invoked concurrently.
 * Note, that Rx 2.x [Observable] **does not support backpressure**. Use [rxFlowable].
 *
 * | **Coroutine action**                         | **Signal to subscriber**
 * | -------------------------------------------- | ------------------------
 * | `send`                                       | `onNext`
 * | Normal completion or `close` without cause   | `onComplete`
 * | Failure with exception or `close` with cause | `onError`
 */
public fun <T> rxObservable(
    context: CoroutineContext,
    block: suspend ProducerScope<T>.() -> Unit
): Observable<T> = Observable.create { subscriber ->
    val newContext = newCoroutineContext(context)
    val coroutine = RxObservableCoroutine(newContext, subscriber)
    coroutine.initParentJob(context[Job])
    subscriber.setCancellable(coroutine) // do it first (before starting coroutine), to await unnecessary suspensions
    block.startCoroutine(coroutine, coroutine)
}

private class RxObservableCoroutine<T>(
    parentContext: CoroutineContext,
    private val subscriber: ObservableEmitter<T>
) : AbstractCoroutine<Unit>(parentContext, true), ProducerScope<T>, Cancellable {
    override val channel: SendChannel<T> get() = this

    // Mutex is locked when while subscriber.onXXX is being invoked
    private val mutex = Mutex()

    @Volatile
    private var signal: Int = OPEN

    companion object {
        private val SIGNAL = AtomicIntegerFieldUpdater
            .newUpdater(RxObservableCoroutine::class.java, "signal")

        private const val CLOSED_MESSAGE = "This subscription had already closed (completed or failed)"
        private const val OPEN = 0        // open channel, still working
        private const val CLOSED = -1     // closed, but have not signalled onCompleted/onError yet
        private const val SIGNALLED = -2  // already signalled subscriber onCompleted/onError
    }

    override val isClosedForSend: Boolean get() = isCompleted
    override val isFull: Boolean = mutex.isLocked
    override fun close(cause: Throwable?): Boolean = cancel(cause)

    private fun sendException() =
        (state as? CompletedExceptionally)?.cause ?: ClosedSendChannelException(CLOSED_MESSAGE)

    override fun offer(element: T): Boolean {
        if (!mutex.tryLock()) return false
        doLockedNext(element)
        return true
    }

    public suspend override fun send(element: T): Unit {
        // fast-path -- try send without suspension
        if (offer(element)) return
        // slow-path does suspend
        return sendSuspend(element)
    }

    private suspend fun sendSuspend(element: T) {
        mutex.lock()
        doLockedNext(element)
    }

    override fun <R> registerSelectSend(select: SelectInstance<R>, element: T, block: suspend () -> R) =
        mutex.registerSelectLock(select, null) {
            doLockedNext(element)
            block()
        }

    // assert: mutex.isLocked()
    private fun doLockedNext(elem: T) {
        // check if already closed for send
        if (isCancelledOrCompleted) {
            doLockedSignalCompleted()
            throw sendException()
        }
        // notify subscriber
        try {
            subscriber.onNext(elem)
        } catch (e: Throwable) {
            try {
                if (!cancel(e))
                    handleCoroutineException(context, e)
            } finally {
                doLockedSignalCompleted()
            }
            throw sendException()
        }
        /*
           There is no sense to check for `isCompleted` before doing `unlock`, because completion might
           happen after this check and before `unlock` (see `afterCompleted` that does not do anything
           if it fails to acquire the lock that we are still holding).
           We have to recheck `isCompleted` after `unlock` anyway.
         */
        mutex.unlock()
        // recheck isCancelledOrCompleted
        if (isCancelledOrCompleted && mutex.tryLock())
            doLockedSignalCompleted()
    }

    // assert: mutex.isLocked()
    private fun doLockedSignalCompleted() {
        try {
            if (signal >= CLOSED) {
                signal = SIGNALLED // we'll signal onError/onCompleted (that the final state -- no CAS needed)
                val cause = getCompletionCause()
                try {
                    if (cause != null)
                        subscriber.onError(cause)
                    else
                        subscriber.onComplete()
                } catch (e: Throwable) {
                    handleCoroutineException(context, e)
                }
            }
        } finally {
            mutex.unlock()
        }
    }

    override fun onCancellation() {
        if (!SIGNAL.compareAndSet(this, OPEN, CLOSED)) return // abort, other thread invoked doLockedSignalCompleted
        if (mutex.tryLock()) // if we can acquire the lock
            doLockedSignalCompleted()
    }

    // Cancellable impl
    override fun cancel() { cancel(cause = null) }
}