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

import io.reactivex.Single
import io.reactivex.SingleEmitter
import io.reactivex.functions.Cancellable
import kotlinx.coroutines.experimental.AbstractCoroutine
import kotlinx.coroutines.experimental.CoroutineScope
import kotlinx.coroutines.experimental.Job
import kotlinx.coroutines.experimental.newCoroutineContext
import kotlin.coroutines.experimental.CoroutineContext
import kotlin.coroutines.experimental.startCoroutine

/**
 * Creates cold [single][Single] that will run a given [block] in a coroutine.
 * Every time the returned observable is subscribed, it starts a new coroutine in the specified [context].
 * Coroutine returns a single value. Unsubscribing cancels running coroutine.
 *
 * | **Coroutine action**                  | **Signal to subscriber**
 * | ------------------------------------- | ------------------------
 * | Returns a value                       | `onSuccess`
 * | Failure with exception or unsubscribe | `onError`
 */
public fun <T> rxSingle(
    context: CoroutineContext,
    block: suspend CoroutineScope.() -> T
): Single<T> = Single.create { subscriber ->
    val newContext = newCoroutineContext(context)
    val coroutine = RxSingleCoroutine(newContext, subscriber)
    coroutine.initParentJob(context[Job])
    subscriber.setCancellable(coroutine)
    block.startCoroutine(coroutine, coroutine)
}

private class RxSingleCoroutine<T>(
    parentContext: CoroutineContext,
    private val subscriber: SingleEmitter<T>
) : AbstractCoroutine<T>(parentContext, true), Cancellable {
    @Suppress("UNCHECKED_CAST")
    override fun afterCompletion(state: Any?, mode: Int) {
        if (subscriber.isDisposed) return
        if (state is CompletedExceptionally)
            subscriber.onError(state.exception)
        else
            subscriber.onSuccess(state as T)
    }

    // Cancellable impl
    override fun cancel() { cancel(cause = null) }
}
