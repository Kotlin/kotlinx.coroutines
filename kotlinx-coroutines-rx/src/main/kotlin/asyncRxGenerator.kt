package kotlinx.coroutines

import rx.Observable
import rx.Producer
import rx.Subscriber
import java.util.concurrent.atomic.AtomicLongFieldUpdater
import kotlin.coroutines.Continuation
import kotlin.coroutines.CoroutineIntrinsics
import kotlin.coroutines.createCoroutine

/**
 * Scope for [asyncRxGenerate] block.
 */
public abstract class AsyncRxGenerator<in T> internal constructor() {
    public abstract suspend fun emit(item: T)
}

/**
 * Creates cold observable for with a suspending [block].
 * Every time the returned observable is subscribed, it start a new coroutine to emit items with
 * [AsyncRxGenerator.emit]. The generator coroutine is suspended appropriately when subscribers apply back-pressure.
 */
public fun <T> asyncRxGenerate(block: suspend AsyncRxGenerator<T>.() -> Unit): Observable<T> {
    return Observable.create { subscriber ->
        val scope = AsyncRxGeneratorImpl<T>(subscriber)
        scope.next = block.createCoroutine(receiver = scope, completion = scope)
        subscriber.setProducer(scope)
    }
}

private class AsyncRxGeneratorImpl<T>(val subscriber: Subscriber<in T>) : AsyncRxGenerator<T>(), Continuation<Unit>, Producer {
    lateinit var next: Continuation<Unit>

    @Volatile
    private var nRequested: Long = 0

    companion object {
        @JvmStatic
        private val N_REQUESTED_UPDATER = AtomicLongFieldUpdater
            .newUpdater(AsyncRxGeneratorImpl::class.java, "nRequested")
    }

    private fun cas(expect: Long, update: Long) = N_REQUESTED_UPDATER.compareAndSet(this, expect, update)

    // emit, resume, resumeWithException are coroutine methods that are called _sequentially_ in a coroutine

    public suspend override fun emit(item: T): Unit = CoroutineIntrinsics.suspendCoroutineOrReturn sc@ { c ->
        subscriber.onNext(item) // pass item to observer
        while (true) { // lock-free loop for nRequested
            val cur = nRequested
            check(cur > 0)
            if (cur == Long.MAX_VALUE) return@sc Unit // emit more
            val upd = cur - 1
            if (upd == 0L) next = c // assign next _first_, because we'll suspend on cas
            if (cas(cur, upd)) {
                return@sc if (upd == 0L) CoroutineIntrinsics.SUSPENDED else Unit
            }
        }
    }

    override fun resume(value: Unit) {
        subscriber.onCompleted()
    }

    override fun resumeWithException(exception: Throwable) {
        subscriber.onError(exception)
    }

    // request may come _concurrently_ with generating coroutine

    override fun request(n: Long) {
        require(n >= 0)
        while (true) { // lock-free loop for nRequested
            val cur = nRequested
            var upd = cur + n
            if (upd < 0 || n == Long.MAX_VALUE)
                upd = Long.MAX_VALUE
            if (cur == upd) return
            if (cas(cur, upd)) {
                if (cur == 0L) next.resume(Unit)
                return
            }
        }
    }
}
