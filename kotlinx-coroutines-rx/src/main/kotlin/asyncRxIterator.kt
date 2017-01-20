package kotlinx.coroutines

import rx.Observable
import rx.Subscriber
import java.util.concurrent.atomic.AtomicReferenceFieldUpdater
import kotlin.coroutines.Continuation
import kotlin.coroutines.CoroutineIntrinsics

/**
 * Suspending iteration extension. It does not have its own buffer and works by arranging rendezvous between
 * producer and consumer. It applies back-pressure to the producer as needed. If iterating coroutine does not have a
 * dispatcher with its own thread, then the iterating coroutine is resumed and works in the thread that governs
 * producer observable.
 */
public suspend operator fun <V : Any> Observable<V>.iterator(): ObservableIterator<V> {
    val iterator = ObservableIterator<V>()
    subscribe(iterator)
    return iterator
}

private sealed class Waiter<in T>(val c: Continuation<T>)
private class HasNextWaiter(c: Continuation<Boolean>) : Waiter<Boolean>(c)
private class NextWaiter<V>(c: Continuation<V>) : Waiter<V>(c)

private object Completed
private class CompletedWith(val v: Any)
private class Error(val e: Throwable)

public class ObservableIterator<V : Any> : Subscriber<V>() {
    // Contains either null, Completed, CompletedWith, Error(exception), Waiter, or next value
    @Volatile
    private var rendezvous: Any? = null

    companion object {
        private val RENDEZVOUS_UPDATER = AtomicReferenceFieldUpdater
            .newUpdater(ObservableIterator::class.java, Any::class.java, "rendezvous")
    }

    private fun cas(expect: Any?, update: Any?) = RENDEZVOUS_UPDATER.compareAndSet(this, expect, update)

    @Suppress("UNCHECKED_CAST")
    public suspend operator fun hasNext(): Boolean = CoroutineIntrinsics.suspendCoroutineOrReturn sc@ { c ->
        while (true) { // lock-free loop for rendezvous
            val cur = rendezvous
            when (cur) {
                null -> if (cas(null, HasNextWaiter(c))) return@sc CoroutineIntrinsics.SUSPENDED
                Completed -> return@sc false
                is CompletedWith -> return@sc true
                is Error -> throw cur.e
                is Waiter<*> -> throw IllegalStateException("Concurrent iteration")
                else -> return@sc true
            }
        }
    }

    @Suppress("UNCHECKED_CAST")
    public suspend operator fun next(): V = CoroutineIntrinsics.suspendCoroutineOrReturn sc@ { c ->
        while (true) { // lock-free loop for rendezvous
            val cur = rendezvous
            when (cur) {
                null -> if (cas(null, NextWaiter(c))) return@sc CoroutineIntrinsics.SUSPENDED
                Completed -> throw NoSuchElementException()
                is CompletedWith -> if (cas(cur, Completed)) return@sc cur.v as V
                is Error -> throw cur.e
                is Waiter<*> -> throw IllegalStateException("Concurrent iteration")
                else -> if (cas(cur, null)) return (cur as V).apply { request(1) }
            }
        }
    }

    public override fun onStart() {
        request(1)
    }

    public override fun onError(e: Throwable) {
        while (true) { // lock-free loop for rendezvous
            val cur = rendezvous
            when (cur) {
                null ->  if (cas(null, Error(e))) return
                Completed -> throw IllegalStateException("onError after onCompleted")
                is CompletedWith -> throw IllegalStateException("onError after onCompleted")
                is Error -> throw IllegalStateException("onError after onError")
                is Waiter<*> -> if (cas(cur, null)) {
                    cur.c.resumeWithException(e)
                    return
                }
                else -> throw IllegalStateException("onError after onNext before request(1) was called")
            }
        }
    }

    @Suppress("UNCHECKED_CAST")
    public override fun onNext(v: V) {
        while (true) { // lock-free loop for rendezvous
            val cur = rendezvous
            when (cur) {
                null ->  if (cas(null, v)) return
                Completed -> throw IllegalStateException("onNext after onCompleted")
                is CompletedWith -> throw IllegalStateException("onNext after onCompleted")
                is Error -> throw IllegalStateException("onNext after onError")
                is HasNextWaiter -> if (cas(cur, v)) {
                    cur.c.resume(true)
                    return
                }
                is NextWaiter<*> -> if (cas(cur, null)) {
                    (cur as NextWaiter<V>).c.resume(v)
                    return
                }
                else -> throw IllegalStateException("onNext after onNext before request(1) was called")
            }
        }
    }

    public override fun onCompleted() {
        while (true) { // lock-free loop for rendezvous
            val cur = rendezvous
            when (cur) {
                null ->  if (cas(null, Completed)) return
                Completed -> throw IllegalStateException("onCompleted after onCompleted")
                is CompletedWith -> throw IllegalStateException("onCompleted after onCompleted")
                is Error -> throw IllegalStateException("onCompleted after onError")
                is HasNextWaiter -> if (cas(cur, Completed)) {
                    cur.c.resume(false)
                    return
                }
                is NextWaiter<*> -> if (cas(cur, Completed)) {
                    cur.c.resumeWithException(NoSuchElementException())
                    return
                }
                else -> if (cas(cur, CompletedWith(cur))) return
            }
        }
    }
}
