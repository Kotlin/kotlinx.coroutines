package kotlinx.coroutines

import rx.Observable
import rx.Subscriber
import java.util.concurrent.atomic.AtomicReference
import kotlin.coroutines.Continuation
import kotlin.coroutines.suspendCoroutine

// supports suspending iteration on observables
suspend operator fun <V : Any> Observable<V>.iterator(): ObserverIterator<V> {
    val iterator = ObserverIterator<V>()
    subscribe(iterator.subscriber)
    return iterator
}

private sealed class Waiter<in T>(val c: Continuation<T>)
private class HasNextWaiter(c: Continuation<Boolean>) : Waiter<Boolean>(c)
private class NextWaiter<V>(c: Continuation<V>) : Waiter<V>(c)

private object Complete
private class Fail(val e: Throwable)

class ObserverIterator<V : Any> {
    internal val subscriber = Sub()
    // Contains either null, Complete, Fail(exception), Waiter, or next value
    private val rendezvous = AtomicReference<Any?>()

    @Suppress("UNCHECKED_CAST")
    private suspend fun awaitHasNext(): Boolean = suspendCoroutine sc@ { c ->
        while (true) { // lock-free loop for rendezvous
            val cur = rendezvous.get()
            when (cur) {
                null -> {
                    if (rendezvous.compareAndSet(null, HasNextWaiter(c))) return@sc
                }
                Complete -> {
                    c.resume(false)
                    return@sc
                }
                is Fail -> {
                    c.resumeWithException(cur.e)
                    return@sc
                }
                is Waiter<*> -> {
                    c.resumeWithException(IllegalStateException("Concurrent iteration"))
                    return@sc
                }
                else -> {
                    c.resume(true)
                    return@sc
                }
            }
        }
    }

    private suspend fun awaitNext(): V = suspendCoroutine sc@ { c ->
        while (true) { // lock-free loop for rendezvous
            val cur = rendezvous.get()
            when (cur) {
                null -> {
                    if (rendezvous.compareAndSet(null, NextWaiter(c))) return@sc
                }
                Complete -> {
                    c.resumeWithException(NoSuchElementException())
                    return@sc
                }
                is Fail -> {
                    c.resumeWithException(cur.e)
                    return@sc
                }
                is Waiter<*> -> {
                    c.resumeWithException(IllegalStateException("Concurrent iteration"))
                    return@sc
                }
                else -> {
                    if (rendezvous.compareAndSet(cur, null)) {
                        c.resume(consumeValue(cur))
                        return@sc
                    }
                }
            }
        }
    }

    suspend operator fun hasNext(): Boolean {
        val cur = rendezvous.get()
        return when (cur) {
            null ->  awaitHasNext()
            Complete -> false
            is Fail -> throw cur.e
            is Waiter<*> -> throw IllegalStateException("Concurrent iteration")
            else -> true
        }
    }

    suspend operator fun next(): V {
        while (true) { // lock-free loop for rendezvous
            val cur = rendezvous.get()
            when (cur) {
                null ->  return awaitNext()
                Complete -> throw NoSuchElementException()
                is Fail -> throw cur.e
                is Waiter<*> -> throw IllegalStateException("Concurrent iteration")
                else -> if (rendezvous.compareAndSet(cur, null)) return consumeValue(cur)
            }
        }
    }

    @Suppress("UNCHECKED_CAST")
    private fun consumeValue(cur: Any?): V {
        subscriber.requestOne()
        return cur as V
    }

    internal inner class Sub : Subscriber<V>() {
        fun requestOne() {
            request(1)
        }

        override fun onStart() {
            requestOne()
        }

        override fun onError(e: Throwable) {
            while (true) { // lock-free loop for rendezvous
                val cur = rendezvous.get()
                when (cur) {
                    null ->  if (rendezvous.compareAndSet(null, Fail(e))) return
                    Complete -> throw IllegalStateException("onError after onComplete")
                    is Fail -> throw IllegalStateException("onError after onError")
                    is Waiter<*> -> if (rendezvous.compareAndSet(cur, null)) {
                        cur.c.resumeWithException(e)
                        return
                    }
                    else -> throw IllegalStateException("onError after onNext before request(1) was called")
                }
            }
        }

        @Suppress("UNCHECKED_CAST")
        override fun onNext(v: V) {
            while (true) { // lock-free loop for rendezvous
                val cur = rendezvous.get()
                when (cur) {
                    null ->  if (rendezvous.compareAndSet(null, v)) return
                    Complete -> throw IllegalStateException("onNext after onComplete")
                    is Fail -> throw IllegalStateException("onNext after onError")
                    is HasNextWaiter -> if (rendezvous.compareAndSet(cur, v)) {
                        cur.c.resume(true)
                        return
                    }
                    is NextWaiter<*> -> if (rendezvous.compareAndSet(cur, null)) {
                        (cur as NextWaiter<V>).c.resume(v)
                        return
                    }
                    else -> throw IllegalStateException("onNext after onNext before request(1) was called")
                }
            }
        }

        override fun onCompleted() {
            while (true) { // lock-free loop for rendezvous
                val cur = rendezvous.get()
                when (cur) {
                    null ->  if (rendezvous.compareAndSet(null, Complete)) return
                    Complete -> throw IllegalStateException("onComplete after onComplete")
                    is Fail -> throw IllegalStateException("onComplete after onError")
                    is HasNextWaiter -> if (rendezvous.compareAndSet(cur, Complete)) {
                        cur.c.resume(false)
                        return
                    }
                    is NextWaiter<*> -> if (rendezvous.compareAndSet(cur, Complete)) {
                        cur.c.resumeWithException(NoSuchElementException())
                        return
                    }
                    else -> throw IllegalStateException("onComplete after onNext before request(1) was called")
                }
            }
        }
    }
}
