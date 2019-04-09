/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("unused", "DeprecatedCallableAddReplaceWith", "UNUSED_PARAMETER")
package kotlinx.coroutines.flow

import kotlin.coroutines.*

/**
 * These deprecations are added to improve user experience when they will start to
 * search for their favourite operators and/or patterns that are missing or renamed in Flow.
 */

/** @suppress **/
@Deprecated(message = "Use flowWith or flowOn instead", level = DeprecationLevel.ERROR)
public fun <T> Flow<T>.subscribeOn(context: CoroutineContext): Flow<T> = error("Should not be called")

/** @suppress **/
@Deprecated(message = "Use flowWith or flowOn instead", level = DeprecationLevel.ERROR)
public fun <T> Flow<T>.observeOn(context: CoroutineContext): Flow<T> = error("Should not be called")

/** @suppress **/
@Deprecated(message = "Use flowWith or flowOn instead", level = DeprecationLevel.ERROR)
public fun <T> Flow<T>.publishOn(context: CoroutineContext): Flow<T> = error("Should not be called")

/** @suppress **/
@Deprecated(message = "Use BroadcastChannel.asFlow()", level = DeprecationLevel.ERROR)
public fun BehaviourSubject(): Any = error("Should not be called")

/** @suppress **/
@Deprecated(
    message = "ReplaySubject is not supported. The closest analogue is buffered broadcast channel",
    level = DeprecationLevel.ERROR)
public fun ReplaySubject(): Any = error("Should not be called")

/** @suppress **/
@Deprecated(message = "PublishSubject is not supported", level = DeprecationLevel.ERROR)
public fun PublishSubject(): Any = error("Should not be called")

/** @suppress **/
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow analogue is named onErrorCollect",
    replaceWith = ReplaceWith("onErrorCollect(fallback)")
)
public fun <T> Flow<T>.onErrorResume(fallback: Flow<T>): Flow<T> = error("Should not be called")


/** @suppress **/
@Suppress("UNUSED_PARAMETER", "UNUSED", "DeprecatedCallableAddReplaceWith")
@Deprecated(message = "withContext in flow body is deprecated, use flowOn instead", level = DeprecationLevel.ERROR)
public fun <T, R> FlowCollector<T>.withContext(context: CoroutineContext, block: suspend () -> R): Unit = error("Should not be called")


/** @suppress **/
@Deprecated(message = "Use launch + collect instead", level = DeprecationLevel.ERROR)
public fun <T> Flow<T>.subscribe(): Unit = error("Should not be called")

/** @suppress **/
@Deprecated(message = "Use launch + collect instead", level = DeprecationLevel.ERROR)
public fun <T> Flow<T>.subscribe(onEach: (T) -> Unit): Unit = error("Should not be called")

/** @suppress **/
@Deprecated(message = "Use launch + collect instead", level = DeprecationLevel.ERROR)
public fun <T> Flow<T>.subscribe(onEach: (T) -> Unit, onError: (Throwable) -> Unit): Unit = error("Should not be called")


/**
 * Note that this replacement is sequential (`concat`) by default.
 * For concurrent flatMap [flatMapMerge] can be used instead.
 * @suppress
 */
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow analogue is named flatMapConcat",
    replaceWith = ReplaceWith("flatMapConcat(mapper)")
)
public fun <T, R> Flow<T>.flatMap(mapper: suspend (T) -> Flow<R>): Flow<R> = error("Should not be called")

/** @suppress **/
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow analogue is named flatMapConcat",
    replaceWith = ReplaceWith("flatMapConcat(mapper)")
)
public fun <T, R> Flow<T>.concatMap(mapper: (T) -> Flow<R>): Flow<R> = error("Should not be called")


/**
 * Note that this replacement is sequential (`concat`) by default.
 * For concurrent flatMap [flattenMerge] can be used instead.
 * @suppress
 */
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow analogue is named flattenConcat",
    replaceWith = ReplaceWith("flattenConcat()")
)
public fun <T> Flow<Flow<T>>.merge(): Flow<T> = error("Should not be called")

/** @suppress **/
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow analogue is named flattenConcat",
    replaceWith = ReplaceWith("flattenConcat()")
)
public fun <T> Flow<Flow<T>>.flatten(): Flow<T> = error("Should not be called")
