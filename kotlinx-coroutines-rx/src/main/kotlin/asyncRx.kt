package kotlinx.coroutines

import rx.Observable
import rx.subjects.AsyncSubject

/**
 * Run asynchronous computations based on [c] coroutine parameter
 *
 * Execution starts immediately within the 'asyncRx' call and it runs until
 * the first suspension point is reached ('*await' call for some Observable instance).
 * Remaining part of coroutine will be executed as it's passed into 'subscribe'
 * call of awaited Observable.
 *
 * @param c a coroutine representing reactive computations
 *
 * @return Observable with single value containing expression returned from coroutine
 */
fun <T> asyncRx(
        coroutine c: Controller<T>.() -> Continuation<Unit>
): Observable<T> {
    val controller = Controller<T>()
    c(controller).resume(Unit)

    return controller.result
}

class Controller<T> internal constructor() {
    internal val result: AsyncSubject<T> = AsyncSubject.create<T>()

    suspend fun <V> Observable<V>.awaitFirst(x: Continuation<V>) {
        this.first().subscribeWithContinuation(x)
    }

    suspend fun <V> Observable<V>.awaitLast(x: Continuation<V>) {
        this.last().subscribeWithContinuation(x)
    }

    suspend fun <V> Observable<V>.awaitSingle(x: Continuation<V>) {
        this.single().subscribeWithContinuation(x)
    }

    private fun <V> Observable<V>.subscribeWithContinuation(x: Continuation<V>) {
        subscribe(x::resume, x::resumeWithException)
    }

    suspend fun <V> Observable<V>.applyForEachAndAwait(
            block: (V) -> Unit,
            x: Continuation<Unit>
    ) {
        this.subscribe(block, x::resumeWithException, { x.resume(Unit) })
    }

    operator fun handleResult(v: T, x: Continuation<Nothing>) {
        result.onNext(v)
        result.onCompleted()
    }

    operator fun handleException(t: Throwable, x: Continuation<Nothing>) {
        result.onError(t)
    }
}
