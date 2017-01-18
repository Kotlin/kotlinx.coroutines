package kotlinx.coroutines.experimental.rx

import rx.Observable
import rx.subjects.AsyncSubject
import kotlin.coroutines.*

/**
 * Run asynchronous computations based on [block] coroutine parameter
 *
 * Execution starts immediately within the 'asyncRx' call and it runs until
 * the first suspension point is reached ('*await' call for some Observable instance).
 * Remaining part of coroutine will be executed as it's passed into 'subscribe'
 * call of awaited Observable.
 *
 * @param block a coroutine representing reactive computations
 *
 * @return Observable with single value containing expression returned from coroutine
 */
fun <T> rxSingle(
    context: CoroutineContext = EmptyCoroutineContext,
    block: suspend () -> T
): Observable<T> {
    val result: AsyncSubject<T> = AsyncSubject.create<T>()
    block.startCoroutine(
            object: Continuation<T> {
                override val context: CoroutineContext = context
                override fun resumeWithException(exception: Throwable) {
                    result.onError(exception)
                }

                override fun resume(data: T) {
                    result.onNext(data)
                    result.onCompleted()
                }
            }
    )
    return result
}

suspend fun <V> Observable<V>.awaitFirst(): V = first().awaitOne()

suspend fun <V> Observable<V>.awaitLast(): V = last().awaitOne()

suspend fun <V> Observable<V>.awaitSingle(): V = single().awaitOne()

private suspend fun <V> Observable<V>.awaitOne(): V = suspendCoroutine<V> { x ->
    subscribe(x::resume, x::resumeWithException)
}

suspend fun <V> Observable<V>.applyForEachAndAwait(
        block: (V) -> Unit
) = suspendCoroutine<Unit> { x->
    this.subscribe(block, x::resumeWithException, { x.resume(Unit) })
}
