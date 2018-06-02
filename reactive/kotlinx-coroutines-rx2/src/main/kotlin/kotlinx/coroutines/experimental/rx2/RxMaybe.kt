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

import io.reactivex.*
import io.reactivex.functions.*
import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*

/**
 * Creates cold [maybe][Maybe] that will run a given [block] in a coroutine.
 * Every time the returned observable is subscribed, it starts a new coroutine.
 * Coroutine returns a single, possibly null value. Unsubscribing cancels running coroutine.
 *
 * | **Coroutine action**                  | **Signal to subscriber**
 * | ------------------------------------- | ------------------------
 * | Returns a non-null value              | `onSuccess`
 * | Returns a null                        | `onComplete`
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
public fun <T> rxMaybe(
    context: CoroutineContext = DefaultDispatcher,
    parent: Job? = null,
    block: suspend CoroutineScope.() -> T?
): Maybe<T> = Maybe.create { subscriber ->
    val newContext = newCoroutineContext(context, parent)
    val coroutine = RxMaybeCoroutine(newContext, subscriber)
    subscriber.setCancellable(coroutine)
    coroutine.start(CoroutineStart.DEFAULT, coroutine, block)
}

/** @suppress **Deprecated**: Binary compatibility */
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
@JvmOverloads // for binary compatibility with older code compiled before context had a default
public fun <T> rxMaybe(
    context: CoroutineContext = DefaultDispatcher,
    block: suspend CoroutineScope.() -> T?
): Maybe<T> =
    rxMaybe(context, block = block)

private class RxMaybeCoroutine<T>(
    parentContext: CoroutineContext,
    private val subscriber: MaybeEmitter<T>
) : AbstractCoroutine<T>(parentContext, true), Cancellable {
    override fun onCompleted(value: T) {
        if (!subscriber.isDisposed) {
            if (value == null) subscriber.onComplete() else subscriber.onSuccess(value)
        }
    }

    override fun onCompletedExceptionally(exception: Throwable) {
        if (!subscriber.isDisposed) subscriber.onError(exception)
    }

    // Cancellable impl
    override fun cancel() { cancel(cause = null) }
}
