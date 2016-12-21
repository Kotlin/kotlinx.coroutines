package kotlinx.coroutines

import rx.Observable
import rx.Subscriber
import java.util.concurrent.atomic.AtomicReference
import kotlin.coroutines.Continuation
import kotlin.coroutines.CoroutineIntrinsics.SUSPENDED
import kotlin.coroutines.CoroutineIntrinsics.suspendCoroutineOrReturn

/**
 * Suspending iteration extension. It does not have its own buffer and applies back-pressure to the source.
 * If iterating coroutine does not have a dispatcher with its own thread, then the iterating coroutine
 * is resumed in the thread that invokes [Subscriber.onNext].
 */
suspend operator fun <V : Any> Observable<V>.iterator(): ObserverIterator<V> {
    val iterator = ObserverIterator<V>()
    subscribe(iterator.subscriber)
    return iterator
}

private sealed class Waiter<in T>(val c: Continuation<T>)
private class HasNextWaiter(c: Continuation<Boolean>) : Waiter<Boolean>(c)
private class NextWaiter<V>(c: Continuation<V>) : Waiter<V>(c)

private object Completed
private class CompletedWith(val v: Any)
private class Error(val e: Throwable)

class ObserverIterator<V : Any> {
    internal val subscriber = Sub()
    // Contains either null, Completed, CompletedWith, Error(exception), Waiter, or next value
    private val rendezvous = AtomicReference<Any?>()

    @Suppress("UNCHECKED_CAST")
    suspend operator fun hasNext(): Boolean = suspendCoroutineOrReturn sc@ { c ->
        while (true) { // lock-free loop for rendezvous
            val cur = rendezvous.get()
            when (cur) {
                null -> if (rendezvous.compareAndSet(null, HasNextWaiter(c))) return@sc SUSPENDED
                Completed -> return@sc false
                is CompletedWith -> return@sc true
                is Error -> throw cur.e
                is Waiter<*> -> throw IllegalStateException("Concurrent iteration")
                else -> return@sc true
            }
        }
    }

    @Suppress("UNCHECKED_CAST")
    suspend operator fun next(): V = suspendCoroutineOrReturn sc@ { c ->
        while (true) { // lock-free loop for rendezvous
            val cur = rendezvous.get()
            when (cur) {
                null -> if (rendezvous.compareAndSet(null, NextWaiter(c))) return@sc SUSPENDED
                Completed -> throw NoSuchElementException()
                is CompletedWith -> if (rendezvous.compareAndSet(cur, Completed)) return@sc cur.v as V
                is Error -> throw cur.e
                is Waiter<*> -> throw IllegalStateException("Concurrent iteration")
                else -> if (rendezvous.compareAndSet(cur, null)) return (cur as V).apply { subscriber.requestOne() }
            }
        }
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
                    null ->  if (rendezvous.compareAndSet(null, Error(e))) return
                    Completed -> throw IllegalStateException("onError after onCompleted")
                    is CompletedWith -> throw IllegalStateException("onError after onCompleted")
                    is Error -> throw IllegalStateException("onError after onError")
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
                    Completed -> throw IllegalStateException("onNext after onCompleted")
                    is CompletedWith -> throw IllegalStateException("onNext after onCompleted")
                    is Error -> throw IllegalStateException("onNext after onError")
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
                    null ->  if (rendezvous.compareAndSet(null, Completed)) return
                    Completed -> throw IllegalStateException("onCompleted after onCompleted")
                    is CompletedWith -> throw IllegalStateException("onCompleted after onCompleted")
                    is Error -> throw IllegalStateException("onCompleted after onError")
                    is HasNextWaiter -> if (rendezvous.compareAndSet(cur, Completed)) {
                        cur.c.resume(false)
                        return
                    }
                    is NextWaiter<*> -> if (rendezvous.compareAndSet(cur, Completed)) {
                        cur.c.resumeWithException(NoSuchElementException())
                        return
                    }
                    else -> if (rendezvous.compareAndSet(cur, CompletedWith(cur))) return
                }
            }
        }
    }
}
