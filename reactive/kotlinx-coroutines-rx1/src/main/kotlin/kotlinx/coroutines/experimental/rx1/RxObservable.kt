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

package kotlinx.coroutines.experimental.rx1

import kotlinx.coroutines.experimental.AbstractCoroutine
import kotlinx.coroutines.experimental.Job
import kotlinx.coroutines.experimental.channels.ClosedSendChannelException
import kotlinx.coroutines.experimental.channels.ProducerScope
import kotlinx.coroutines.experimental.channels.SendChannel
import kotlinx.coroutines.experimental.handleCoroutineException
import kotlinx.coroutines.experimental.newCoroutineContext
import kotlinx.coroutines.experimental.selects.SelectInstance
import kotlinx.coroutines.experimental.sync.Mutex
import rx.Observable
import rx.Producer
import rx.Subscriber
import rx.Subscription
import java.util.concurrent.atomic.AtomicLongFieldUpdater
import kotlin.coroutines.experimental.CoroutineContext
import kotlin.coroutines.experimental.startCoroutine

/**
 * Creates cold [Observable] that runs a given [block] in a coroutine.
 * Every time the returned observable is subscribed, it starts a new coroutine in the specified [context].
 * Coroutine emits items with `send`. Unsubscribing cancels running coroutine.
 *
 * Invocations of `send` are suspended appropriately when subscribers apply back-pressure and to ensure that
 * `onNext` is not invoked concurrently.
 *
 * | **Coroutine action**                         | **Signal to subscriber**
 * | -------------------------------------------- | ------------------------
 * | `send`                                       | `onNext`
 * | Normal completion or `close` without cause   | `onCompleted`
 * | Failure with exception or `close` with cause | `onError`
 */
public fun <T> rxObservable(
    context: CoroutineContext,
    block: suspend ProducerScope<T>.() -> Unit
): Observable<T> = Observable.create { subscriber ->
    val newContext = newCoroutineContext(context)
    val coroutine = RxObservableCoroutine(newContext, subscriber)
    coroutine.initParentJob(context[Job])
    subscriber.setProducer(coroutine) // do it first (before starting coroutine), to avoid unnecessary suspensions
    subscriber.add(coroutine)
    block.startCoroutine(coroutine, coroutine)
}

private class RxObservableCoroutine<T>(
    override val parentContext: CoroutineContext,
    private val subscriber: Subscriber<T>
) : AbstractCoroutine<Unit>(true), ProducerScope<T>, Producer, Subscription {
    override val channel: SendChannel<T> get() = this

    // Mutex is locked when either nRequested == 0 or while subscriber.onXXX is being invoked
    private val mutex = Mutex(locked = true)

    @Volatile
    private var nRequested: Long = 0 // < 0 when closed (CLOSED or SIGNALLED)

    companion object {
        private val N_REQUESTED = AtomicLongFieldUpdater
                .newUpdater(RxObservableCoroutine::class.java, "nRequested")

        private const val CLOSED_MESSAGE = "This subscription had already closed (completed or failed)"

        private const val CLOSED = -1L    // closed, but have not signalled onCompleted/onError yet
        private const val SIGNALLED = -2L  // already signalled subscriber onCompleted/onError
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
        if (isCompleted) {
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
        // now update nRequested
        while (true) { // lock-free loop on nRequested
            val cur = nRequested
            if (cur < 0) break // closed from inside onNext => unlock
            if (cur == Long.MAX_VALUE) break // no back-pressure => unlock
            val upd = cur - 1
            if (N_REQUESTED.compareAndSet(this, cur, upd)) {
                if (upd == 0L) return // return to keep locked due to back-pressure
                break // unlock if upd > 0
            }
        }
        /*
           There is no sense to check for `isCompleted` before doing `unlock`, because completion might
           happen after this check and before `unlock` (see `afterCompleted` that does not do anything
           if it fails to acquire the lock that we are still holding).
           We have to recheck `isCompleted` after `unlock` anyway.
         */
        mutex.unlock()
        // recheck isCompleted
        if (isCompleted && mutex.tryLock())
            doLockedSignalCompleted()
    }

    // assert: mutex.isLocked()
    private fun doLockedSignalCompleted() {
        try {
            if (nRequested >= CLOSED) {
                nRequested = SIGNALLED // we'll signal onError/onCompleted (that the final state -- no CAS needed)
                val state = this.state
                try {
                    if (state is CompletedExceptionally && state.cause != null)
                        subscriber.onError(state.cause)
                    else
                        subscriber.onCompleted()
                } catch (e: Throwable) {
                    handleCoroutineException(context, e)
                }
            }
        } finally {
            mutex.unlock()
        }
    }

    override fun request(n: Long) {
        if (n < 0) {
            cancel(IllegalArgumentException("Must request non-negative number, but $n requested"))
            return
        }
        while (true) { // lock-free loop for nRequested
            val cur = nRequested
            if (cur < 0) return // already closed for send, ignore requests
            var upd = cur + n
            if (upd < 0 || n == Long.MAX_VALUE)
                upd = Long.MAX_VALUE
            if (cur == upd) return // nothing to do
            if (N_REQUESTED.compareAndSet(this, cur, upd)) {
                // unlock the mutex when we don't have back-pressure anymore
                if (cur == 0L) {
                    mutex.unlock()
                    // recheck isCompleted
                    if (isCompleted && mutex.tryLock())
                        doLockedSignalCompleted()
                }
                return
            }
        }
    }

    override fun afterCompletion(state: Any?, mode: Int) {
        while (true) { // lock-free loop for nRequested
            val cur = nRequested
            if (cur == SIGNALLED) return // some other thread holding lock already signalled completion
            check(cur >= 0) // no other thread could have marked it as CLOSED, because afterCompletion is invoked once
            if (!N_REQUESTED.compareAndSet(this, cur, CLOSED)) continue // retry on failed CAS
            // Ok -- marked as CLOSED, now can unlock the mutex if it was locked due to backpressure
            if (cur == 0L) {
                doLockedSignalCompleted()
            } else {
                // otherwise mutex was either not locked or locked in concurrent onNext... try lock it to signal completion
                if (mutex.tryLock())
                    doLockedSignalCompleted()
                // Note: if failed `tryLock`, then `doLockedNext` will signal after performing `unlock`
            }
            return // done anyway
        }
    }

    // Subscription impl
    override fun isUnsubscribed(): Boolean = isCompleted
    override fun unsubscribe() { cancel() }
}