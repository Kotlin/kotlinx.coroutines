/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.rx2

import io.reactivex.Flowable
import kotlinx.coroutines.experimental.CoroutineDispatcher
import kotlinx.coroutines.experimental.CoroutineScope
import kotlinx.coroutines.experimental.DefaultDispatcher
import kotlinx.coroutines.experimental.Job
import kotlinx.coroutines.experimental.channels.ProducerScope
import kotlinx.coroutines.experimental.reactive.publish
import kotlin.coroutines.experimental.*

/**
 * Creates cold [flowable][Flowable] that will run a given [block] in a coroutine.
 * Every time the returned flowable is subscribed, it starts a new coroutine.
 * Coroutine emits items with `send`. Unsubscribing cancels running coroutine.
 *
 * Invocations of `send` are suspended appropriately when subscribers apply back-pressure and to ensure that
 * `onNext` is not invoked concurrently.
 *
 * | **Coroutine action**                         | **Signal to subscriber**
 * | -------------------------------------------- | ------------------------
 * | `send`                                       | `onNext`
 * | Normal completion or `close` without cause   | `onComplete`
 * | Failure with exception or `close` with cause | `onError`
 *
 * The [context] for the new coroutine can be explicitly specified.
 * See [CoroutineDispatcher] for the standard context implementations that are provided by `kotlinx.coroutines`.
 * The [coroutineContext] of the parent coroutine may be used,
 * in which case the [Job] of the resulting coroutine is a child of the job of the parent coroutine.
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [DefaultDispatcher] is used.
 *
 * @param context context of the coroutine. The default value is [DefaultDispatcher].
 * @param block the coroutine code.
 */
@JvmOverloads // for binary compatibility with older code compiled before context had a default
public fun <T> rxFlowable(
    context: CoroutineContext = DefaultDispatcher,
    block: suspend ProducerScope<T>.() -> Unit
): Flowable<T> = Flowable.fromPublisher(publish(context, block = block))
