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

import io.reactivex.Maybe
import io.reactivex.MaybeEmitter
import io.reactivex.functions.Cancellable
import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.ContinuationInterceptor
import kotlin.coroutines.experimental.CoroutineContext
import kotlin.coroutines.experimental.startCoroutine

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
 * The [context][CoroutineScope.context] of the parent coroutine from its [scope][CoroutineScope] may be used,
 * in which case the [Job] of the resulting coroutine is a child of the job of the parent coroutine.
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [DefaultDispatcher] is used.
 *
 * @param context context of the coroutine. The default value is [DefaultDispatcher].
 * @param block the coroutine code.
 */
@JvmOverloads // for binary compatibility with older code compiled before context had a default
public fun <T> rxMaybe(
    context: CoroutineContext = DefaultDispatcher,
    block: suspend CoroutineScope.() -> T?
): Maybe<T> = Maybe.create { subscriber ->
    val newContext = newCoroutineContext(context)
    val coroutine = RxMaybeCoroutine(newContext, subscriber)
    coroutine.initParentJob(context[Job])
    subscriber.setCancellable(coroutine)
    block.startCoroutine(coroutine, coroutine)
}

private class RxMaybeCoroutine<T>(
    parentContext: CoroutineContext,
    private val subscriber: MaybeEmitter<T>
) : AbstractCoroutine<T>(parentContext, true), Cancellable {
    @Suppress("UNCHECKED_CAST")
    override fun afterCompletion(state: Any?, mode: Int) {
        if (subscriber.isDisposed) return
        when {
            state is CompletedExceptionally -> subscriber.onError(state.exception)
            state != null                   -> subscriber.onSuccess(state as T)
            else                            -> subscriber.onComplete()
        }
    }

    // Cancellable impl
    override fun cancel() { cancel(cause = null) }
}
