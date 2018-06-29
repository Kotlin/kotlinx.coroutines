/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.rx2

import io.reactivex.*
import io.reactivex.functions.*
import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*

/**
 * Creates cold [single][Single] that will run a given [block] in a coroutine.
 * Every time the returned observable is subscribed, it starts a new coroutine.
 * Coroutine returns a single value. Unsubscribing cancels running coroutine.
 *
 * | **Coroutine action**                  | **Signal to subscriber**
 * | ------------------------------------- | ------------------------
 * | Returns a value                       | `onSuccess`
 * | Failure with exception or unsubscribe | `onError`
 *
 * The [context] for the new coroutine can be explicitly specified.
 * See [CoroutineDispatcher] for the standard context implementations that are provided by `kotlinx.coroutines`.
 * The [coroutineContext] of the parent coroutine may be used,
 * in which case the [Job] of the resulting coroutine is a child of the job of the parent coroutine.
 * The parent job may be also explicitly specified using [parent] parameter.
 *
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [DefaultDispatcher] is used.
 *
 * @param context context of the coroutine. The default value is [DefaultDispatcher].
 * @param parent explicitly specifies the parent job, overrides job from the [context] (if any).
 * @param block the coroutine code.
 */
public fun <T> rxSingle(
    context: CoroutineContext = DefaultDispatcher,
    parent: Job? = null,
    block: suspend CoroutineScope.() -> T
): Single<T> = Single.create { subscriber ->
    val newContext = newCoroutineContext(context, parent)
    val coroutine = RxSingleCoroutine(newContext, subscriber)
    subscriber.setCancellable(coroutine)
    coroutine.start(CoroutineStart.DEFAULT, coroutine, block)
}

/** @suppress **Deprecated**: Binary compatibility */
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
@JvmOverloads // for binary compatibility with older code compiled before context had a default
public fun <T> rxSingle(
    context: CoroutineContext = DefaultDispatcher,
    block: suspend CoroutineScope.() -> T
): Single<T> =
    rxSingle(context, block = block)

private class RxSingleCoroutine<T>(
    parentContext: CoroutineContext,
    private val subscriber: SingleEmitter<T>
) : AbstractCoroutine<T>(parentContext, true), Cancellable {
    override fun onCompleted(value: T) {
        if (!subscriber.isDisposed) subscriber.onSuccess(value)
    }

    override fun onCompletedExceptionally(exception: Throwable) {
        if (!subscriber.isDisposed) subscriber.onError(exception)
    }

    // Cancellable impl
    override fun cancel() { cancel(cause = null) }
}
