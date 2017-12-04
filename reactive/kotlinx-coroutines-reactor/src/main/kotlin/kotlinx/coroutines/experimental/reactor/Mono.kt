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

import kotlinx.coroutines.experimental.*
import reactor.core.Disposable
import reactor.core.publisher.Mono
import reactor.core.publisher.MonoSink
import kotlin.coroutines.experimental.ContinuationInterceptor
import kotlin.coroutines.experimental.CoroutineContext
import kotlin.coroutines.experimental.startCoroutine

/**
 * Creates cold [mono][Mono] that will run a given [block] in a coroutine.
 * Every time the returned mono is subscribed, it starts a new coroutine.
 * Coroutine returns a single, possibly null value. Unsubscribing cancels running coroutine.
 *
 * | **Coroutine action**                  | **Signal to sink**
 * | ------------------------------------- | ------------------------
 * | Returns a non-null value              | `success(value)`
 * | Returns a null                        | `success`
 * | Failure with exception or unsubscribe | `error`
 *
 * The [context] for the new coroutine can be explicitly specified.
 * See [CoroutineDispatcher] for the standard context implementations that are provided by `kotlinx.coroutines`.
 * The [context][CoroutineScope.context] of the parent coroutine from its [scope][CoroutineScope] may be used,
 * in which case the [Job] of the resulting coroutine is a child of the job of the parent coroutine.
 * The parent job may be also explicitly specified using [parent] parameter.
 *
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [DefaultDispatcher] is used.
 *
 * @param context context of the coroutine. The default value is [DefaultDispatcher].
 * @param parent explicitly specifies the parent job, overrides job from the [context] (if any).
 * @param block the coroutine code.
 */
fun <T> mono(
    context: CoroutineContext = DefaultDispatcher,
    parent: Job? = null,
    block: suspend CoroutineScope.() -> T?
): Mono<T> = Mono.create { sink ->
    val newContext = newCoroutineContext(context, parent)
    val coroutine = MonoCoroutine(newContext, sink)
    coroutine.initParentJob(newContext[Job])
    sink.onDispose(coroutine)
    block.startCoroutine(coroutine, coroutine)
}

/** @suppress **Deprecated**: Binary compatibility */
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
@JvmOverloads // for binary compatibility with older code compiled before context had a default
fun <T> mono(
    context: CoroutineContext = DefaultDispatcher,
    block: suspend CoroutineScope.() -> T?
): Mono<T> =
    mono(context, block = block)

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

