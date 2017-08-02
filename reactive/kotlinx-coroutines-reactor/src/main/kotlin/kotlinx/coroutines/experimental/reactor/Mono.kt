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
package kotlinx.coroutines.experimental.reactor

import kotlinx.coroutines.experimental.AbstractCoroutine
import kotlinx.coroutines.experimental.CoroutineScope
import kotlinx.coroutines.experimental.Job
import kotlinx.coroutines.experimental.newCoroutineContext
import reactor.core.Disposable
import reactor.core.publisher.Mono
import reactor.core.publisher.MonoSink
import kotlin.coroutines.experimental.CoroutineContext
import kotlin.coroutines.experimental.startCoroutine

/**
 * Creates cold [mono][Mono] that will run a given [block] in a coroutine.
 * Every time the returned mono is subscribed, it starts a new coroutine in the specified [context].
 * Coroutine returns a single, possibly null value. Unsubscribing cancels running coroutine.
 *
 * | **Coroutine action**                  | **Signal to sink**
 * | ------------------------------------- | ------------------------
 * | Returns a non-null value              | `success(value)`
 * | Returns a null                        | `success`
 * | Failure with exception or unsubscribe | `error`
 */
fun <T> mono(
        context: CoroutineContext,
        block: suspend CoroutineScope.() -> T?
): Mono<T> = Mono.create { sink ->
    val newContext = newCoroutineContext(context)
    val coroutine = MonoCoroutine(newContext, sink)
    coroutine.initParentJob(context[Job])
    sink.onDispose(coroutine)
    block.startCoroutine(coroutine, coroutine)
}

private class MonoCoroutine<in T>(
    parentContext: CoroutineContext,
    private val sink: MonoSink<T>
) : AbstractCoroutine<T>(parentContext, true), Disposable {
    var disposed = false

    @Suppress("UNCHECKED_CAST")
    override fun afterCompletion(state: Any?, mode: Int) {
        when {
            disposed                        -> {}
            state is CompletedExceptionally -> sink.error(state.exception)
            state != null                   -> sink.success(state as T)
            else                            -> sink.success()
        }
    }

    override fun dispose() {
        disposed = true
        cancel(cause = null)
    }

    override fun isDisposed(): Boolean = disposed
}

