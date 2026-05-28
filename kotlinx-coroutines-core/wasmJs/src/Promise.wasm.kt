@file:OptIn(ExperimentalWasmJsInterop::class)
package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.js.*

@OptIn(ExperimentalWasmJsInterop::class)
internal actual fun JsPromiseError.toThrowable(): Throwable = try {
    unsafeCast<JsReference<Throwable>>().get()
} catch (_: Throwable) {
    Exception("Non-Kotlin exception $this of type '${this::class}'")
}

@OptIn(ExperimentalWasmJsInterop::class)
internal actual fun Throwable.toJsPromiseError(): JsPromiseError = toJsReference()

/*
 * All code after this line is preserved for compatibility with versions 1.10.2 and below.
 */

@Suppress("UNUSED_PARAMETER")
private fun promiseSetDeferred(promise: Promise<JsAny?>, deferred: JsAny): Unit =
    js("promise.deferred = deferred")

@Suppress("UNUSED_PARAMETER")
private fun promiseGetDeferred(promise: Promise<JsAny?>): JsAny? = js("""{
    console.assert(promise instanceof Promise, "promiseGetDeferred must receive a promise, but got ", promise);
    return promise.deferred == null ? null : promise.deferred;
}""")

@Deprecated("Moved to the 'web' source set", level = DeprecationLevel.HIDDEN)
public fun <T> CoroutineScope.promise(
    context: CoroutineContext = EmptyCoroutineContext,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend CoroutineScope.() -> T
): Promise<JsAny?> =
    async(context, start, block).oldAsPromiseImpl()

@Deprecated("Moved to the 'web' source set", level = DeprecationLevel.HIDDEN)
public fun <T> Deferred<T>.asPromise(): Promise<JsAny?> = oldAsPromiseImpl()

private fun <T> Deferred<T>.oldAsPromiseImpl(): Promise<JsAny?> {
    val promise = Promise<JsAny?> { resolve, reject ->
        invokeOnCompletion {
            val e = getCompletionExceptionOrNull()
            if (e != null) {
                reject(e.toJsReference())
            } else {
                resolve(getCompleted()?.toJsReference())
            }
        }
    }
    promiseSetDeferred(promise, this.toJsReference())
    return promise
}

@Deprecated("Moved to the 'web' source set", level = DeprecationLevel.HIDDEN)
@Suppress("UNCHECKED_CAST_TO_EXTERNAL_INTERFACE", "UNCHECKED_CAST")
public fun <T> Promise<JsAny?>.asDeferred(): Deferred<T> {
    val deferred = promiseGetDeferred(this) as? JsReference<Deferred<T>>
    return deferred?.get() ?: GlobalScope.async(start = CoroutineStart.UNDISPATCHED) { oldAwaitImpl() }
}

@Deprecated("Moved to the 'web' source set", level = DeprecationLevel.HIDDEN)
public suspend fun <T> Promise<JsAny?>.await(): T = oldAwaitImpl()

@Suppress("UNCHECKED_CAST")
private suspend fun <T> Promise<JsAny?>.oldAwaitImpl(): T = suspendCancellableCoroutine { cont: CancellableContinuation<T> ->
    this@oldAwaitImpl.then(
        onFulfilled = { cont.resume(it as T); null },
        onRejected = { cont.resumeWithException(it.toThrowableOrNull() ?: error("Unexpected non-Kotlin exception $it")); null }
    )
}
