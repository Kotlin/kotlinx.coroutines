/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("unused", "INVISIBLE_REFERENCE", "INVISIBLE_MEMBER", "UNUSED_PARAMETER")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.internal.InlineOnly

/**
 * Applying [cancellable][Flow.cancellable] to a [SharedFlow] has no effect.
 * See the [SharedFlow] documentation on Operator Fusion.
 */
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Applying 'cancellable' to a SharedFlow has no effect. See the SharedFlow documentation on Operator Fusion.",
    replaceWith = ReplaceWith("this")
)
public fun <T> SharedFlow<T>.cancellable(): Flow<T> = noImpl()

/**
 * Applying [flowOn][Flow.flowOn] to [SharedFlow] has no effect.
 * See the [SharedFlow] documentation on Operator Fusion.
 */
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Applying 'flowOn' to SharedFlow has no effect. See the SharedFlow documentation on Operator Fusion.",
    replaceWith = ReplaceWith("this")
)
public fun <T> SharedFlow<T>.flowOn(context: CoroutineContext): Flow<T> = noImpl()

/**
 * Applying [conflate][Flow.conflate] to [StateFlow] has no effect.
 * See the [StateFlow] documentation on Operator Fusion.
 */
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Applying 'conflate' to StateFlow has no effect. See the StateFlow documentation on Operator Fusion.",
    replaceWith = ReplaceWith("this")
)
public fun <T> StateFlow<T>.conflate(): Flow<T> = noImpl()

/**
 * Applying [distinctUntilChanged][Flow.distinctUntilChanged] to [StateFlow] has no effect.
 * See the [StateFlow] documentation on Operator Fusion.
 */
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Applying 'distinctUntilChanged' to StateFlow has no effect. See the StateFlow documentation on Operator Fusion.",
    replaceWith = ReplaceWith("this")
)
public fun <T> StateFlow<T>.distinctUntilChanged(): Flow<T> = noImpl()

@Deprecated(
    message = "isActive is resolved into the extension of outer CoroutineScope which is likely to be an error." +
        "Use currentCoroutineContext().isActive or cancellable() operator instead " +
        "or specify the receiver of isActive explicitly. " +
        "Additionally, flow {} builder emissions are cancellable by default.",
    level = DeprecationLevel.ERROR,
    replaceWith = ReplaceWith("currentCoroutineContext().isActive")
)
public val FlowCollector<*>.isActive: Boolean
    get() = noImpl()

@Deprecated(
    message = "cancel() is resolved into the extension of outer CoroutineScope which is likely to be an error." +
        "Use currentCoroutineContext().cancel() instead or specify the receiver of cancel() explicitly",
    level = DeprecationLevel.ERROR,
    replaceWith = ReplaceWith("currentCoroutineContext().cancel(cause)")
)
public fun FlowCollector<*>.cancel(cause: CancellationException? = null): Unit = noImpl()

@Deprecated(
    message = "coroutineContext is resolved into the property of outer CoroutineScope which is likely to be an error." +
        "Use currentCoroutineContext() instead or specify the receiver of coroutineContext explicitly",
    level = DeprecationLevel.ERROR,
    replaceWith = ReplaceWith("currentCoroutineContext()")
)
public val FlowCollector<*>.coroutineContext: CoroutineContext
    get() = noImpl()

@Deprecated(
    message = "SharedFlow never completes, so this operator typically has not effect, it can only " +
        "catch exceptions from 'onSubscribe' operator",
    level = DeprecationLevel.WARNING,
    replaceWith = ReplaceWith("this")
)
@InlineOnly
public inline fun <T> SharedFlow<T>.catch(noinline action: suspend FlowCollector<T>.(cause: Throwable) -> Unit): Flow<T> =
    (this as Flow<T>).catch(action)

@Deprecated(
    message = "SharedFlow never completes, so this operator has no effect.",
    level = DeprecationLevel.WARNING,
    replaceWith = ReplaceWith("this")
)
@InlineOnly
public inline fun <T> SharedFlow<T>.retry(
    retries: Long = Long.MAX_VALUE,
    noinline predicate: suspend (cause: Throwable) -> Boolean = { true }
): Flow<T> =
    (this as Flow<T>).retry(retries, predicate)

@Deprecated(
    message = "SharedFlow never completes, so this operator has no effect.",
    level = DeprecationLevel.WARNING,
    replaceWith = ReplaceWith("this")
)
@InlineOnly
public inline fun <T> SharedFlow<T>.retryWhen(noinline predicate: suspend FlowCollector<T>.(cause: Throwable, attempt: Long) -> Boolean): Flow<T> =
    (this as Flow<T>).retryWhen(predicate)

@Suppress("DeprecatedCallableAddReplaceWith")
@Deprecated(
    message = "SharedFlow never completes, so this terminal operation never completes.",
    level = DeprecationLevel.WARNING
)
@InlineOnly
public suspend inline fun <T> SharedFlow<T>.toList(): List<T> =
    (this as Flow<T>).toList()

@Suppress("DeprecatedCallableAddReplaceWith")
@Deprecated(
    message = "SharedFlow never completes, so this terminal operation never completes.",
    level = DeprecationLevel.WARNING
)
@InlineOnly
public suspend inline fun <T> SharedFlow<T>.toSet(): Set<T> =
    (this as Flow<T>).toSet()

@Suppress("DeprecatedCallableAddReplaceWith")
@Deprecated(
    message = "SharedFlow never completes, so this terminal operation never completes.",
    level = DeprecationLevel.WARNING
)
@InlineOnly
public suspend inline fun <T> SharedFlow<T>.count(): Int =
    (this as Flow<T>).count()
