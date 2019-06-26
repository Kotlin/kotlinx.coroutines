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

/**
 * `observeOn` has no direct match in [Flow] API because all terminal flow operators are suspending and
 * thus use the context of the caller.
 *
 * For example, the following code:
 * ```
 * flowable
 *     .observeOn(Schedulers.io())
 *     .doOnEach { value -> println("Received $value") }
 *     .subscribe()
 * ```
 *
 *  has the following Flow equivalent:
 * ```
 * withContext(Dispatchers.IO) {
 *     flow.collect { value -> println("Received $value") }
 * }
 *
 * ```
 * @suppress
 */
@Deprecated(message = "Collect flow in the desired context instead", level = DeprecationLevel.ERROR)
public fun <T> Flow<T>.observeOn(context: CoroutineContext): Flow<T> = error("Should not be called")

/**
 * `publishOn` has no direct match in [Flow] API because all terminal flow operators are suspending and
 * thus use the context of the caller.
 *
 * For example, the following code:
 * ```
 * flux
 *     .publishOn(Schedulers.io())
 *     .doOnEach { value -> println("Received $value") }
 *     .subscribe()
 * ```
 *
 *  has the following Flow equivalent:
 * ```
 * withContext(Dispatchers.IO) {
 *     flow.collect { value -> println("Received $value") }
 * }
 *
 * ```
 * @suppress
 */
@Deprecated(message = "Collect flow in the desired context instead", level = DeprecationLevel.ERROR)
public fun <T> Flow<T>.publishOn(context: CoroutineContext): Flow<T> = error("Should not be called")

/**
 * `subscribeOn` has no direct match in [Flow] API because [Flow] preserves its context and does not leak it.
 *
 * For example, the following code:
 * ```
 * flowable
 *     .map { value -> println("Doing map in IO"); value }
 *     .subscribeOn(Schedulers.io())
 *     .observeOn(Schedulers.computation())
 *     .doOnEach { value -> println("Processing $value in computation")
 *     .subscribe()
 * ```
 * has the following Flow equivalent:
 * ```
 * withContext(Dispatchers.Default) {
 *     flow
 *        .map { value -> println("Doing map in IO"); value }
 *        .flowOn(Dispatchers.IO) // Works upstream, doesn't change downstream
 *        .collect { value ->
 *             println("Processing $value in computation")
 *        }
 * }
 * ```
 * Opposed to subscribeOn, it it **possible** to use multiple `flowOn` operators in the one flow
 * @suppress
 */
@Deprecated(message = "Use flowOn instead", level = DeprecationLevel.ERROR)
public fun <T> Flow<T>.subscribeOn(context: CoroutineContext): Flow<T> = error("Should not be called")

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
    message = "Flow analogue of 'onErrorXxx' is 'catch'. Use 'catch { emitAll(fallback) }'",
    replaceWith = ReplaceWith("catch { emitAll(fallback) }")
)
public fun <T> Flow<T>.onErrorResume(fallback: Flow<T>): Flow<T> = error("Should not be called")

@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow analogue of 'onErrorXxx' is 'catch'. Use 'catch { emitAll(fallback) }'",
    replaceWith = ReplaceWith("catch { emitAll(fallback) }")
)
public fun <T> Flow<T>.onErrorResumeNext(fallback: Flow<T>): Flow<T> = error("Should not be called")

/**
 * Self-explanatory, the reason of deprecation is "context preservation" property (you can read more in [Flow] documentation)
 * @suppress
 **/
@Suppress("UNUSED_PARAMETER", "UNUSED", "DeprecatedCallableAddReplaceWith")
@Deprecated(message = "withContext in flow body is deprecated, use flowOn instead", level = DeprecationLevel.ERROR)
public fun <T, R> FlowCollector<T>.withContext(context: CoroutineContext, block: suspend () -> R): Unit = error("Should not be called")

/**
 * `subscribe` is Rx-specific API that has no direct match in flows.
 * One can use [launchIn] instead, for example the following:
 * ```
 * flowable
 *     .observeOn(Schedulers.io())
 *     .subscribe({ println("Received $it") }, { println("Exception $it happened") }, { println("Flowable is completed successfully") }
 * ```
 *
 * has the following Flow equivalent:
 * ```
 * flow
 *     .onEach { value -> println("Received $value") }
 *     .onCompletion { cause -> if (cause == null) println("Flow is completed successfully") }
 *     .catch { cause -> println("Exception $cause happened") }
 *     .flowOn(Dispatchers.IO)
 *     .launchIn(myScope)
 * ```
 *
 * Note that resulting value of [launchIn] is not used because the provided scope takes care of cancellation.
 *
 * Or terminal operators like [single] can be used from suspend functions.
 * @suppress
 */
@Deprecated(
    message = "Use launchIn with onEach, onCompletion and catch operators instead",
    level = DeprecationLevel.ERROR
)
public fun <T> Flow<T>.subscribe(): Unit = error("Should not be called")

/** @suppress **/
@Deprecated(
    message = "Use launchIn with onEach, onCompletion and catch operators instead",
    level = DeprecationLevel.ERROR
)public fun <T> Flow<T>.subscribe(onEach: suspend (T) -> Unit): Unit = error("Should not be called")

/** @suppress **/
@Deprecated(
    message = "Use launchIn with onEach, onCompletion and catch operators instead",
    level = DeprecationLevel.ERROR
)public fun <T> Flow<T>.subscribe(onEach: suspend (T) -> Unit, onError: suspend (Throwable) -> Unit): Unit = error("Should not be called")

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
    message = "Flow analogue of 'merge' is 'flattenConcat'",
    replaceWith = ReplaceWith("flattenConcat()")
)
public fun <T> Flow<Flow<T>>.merge(): Flow<T> = error("Should not be called")

/** @suppress **/
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow analogue of 'flatten' is 'flattenConcat'",
    replaceWith = ReplaceWith("flattenConcat()")
)
public fun <T> Flow<Flow<T>>.flatten(): Flow<T> = error("Should not be called")

/**
 * Kotlin has a built-in generic mechanism for making chained calls.
 * If you wish to write something like
 * ```
 * myFlow.compose(MyFlowExtensions.ignoreErrors()).collect { ... }
 * ```
 * you can replace it with
 *
 * ```
 * myFlow.let(MyFlowExtensions.ignoreErrors()).collect { ... }
 * ```
 *
 * @suppress
 */
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow analogue of 'compose' is 'let'",
    replaceWith = ReplaceWith("let(transformer)")
)
public fun <T, R> Flow<T>.compose(transformer: Flow<T>.() -> Flow<R>): Flow<R> = error("Should not be called")

/**
 * @suppress
 */
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow analogue of 'skip' is 'drop'",
    replaceWith = ReplaceWith("drop(count)")
)
public fun <T> Flow<T>.skip(count: Int): Flow<T> = error("Should not be called")

/**
 * Flow extension to iterate over elements is [collect].
 * Foreach wasn't introduced deliberately to avoid confusion.
 * Flow is not a collection, iteration over it may be not idempotent
 * and can *launch* computations with side-effects.
 * This behaviour is not reflected in [forEach] name.
 * @suppress
 */
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow analogue of 'forEach' is 'collect'",
    replaceWith = ReplaceWith("collect(block)")
)
public fun <T> Flow<T>.forEach(action: suspend (value: T) -> Unit): Unit = error("Should not be called")

@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow has less verbose 'scan' shortcut",
    replaceWith = ReplaceWith("scan(initial, operation)")
)
public fun <T, R> Flow<T>.scanFold(initial: R, @BuilderInference operation: suspend (accumulator: R, value: T) -> R): Flow<R> = error("Should not be called")

@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow analogue of 'onErrorXxx' is 'catch'. Use 'catch { emit(fallback) }'",
    replaceWith = ReplaceWith("catch { emit(fallback) }")
)
// Note: this version without predicate gives better "replaceWith" action
public fun <T> Flow<T>.onErrorReturn(fallback: T): Flow<T> = error("Should not be called")

@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow analogue of 'onErrorXxx' is 'catch'. Use 'catch { e -> if (predicate(e)) emit(fallback) else throw e }'",
    replaceWith = ReplaceWith("catch { e -> if (predicate(e)) emit(fallback) else throw e }")
)
public fun <T> Flow<T>.onErrorReturn(fallback: T, predicate: (Throwable) -> Boolean = { true }): Flow<T> =
    catch { e ->
        // Note: default value is for binary compatibility with preview version, that is why it has body
        if (!predicate(e)) throw e
        emit(fallback)
    }
