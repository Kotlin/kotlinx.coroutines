/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")
@file:Suppress("unused", "DeprecatedCallableAddReplaceWith", "UNUSED_PARAMETER")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.internal.*
import kotlinx.coroutines.flow.internal.unsafeFlow
import kotlin.coroutines.*
import kotlin.jvm.*

/**
 * **GENERAL NOTE**
 *
 * These deprecations are added to improve user experience when they will start to
 * search for their favourite operators and/or patterns that are missing or renamed in Flow.
 * Deprecated functions also are moved here when they renamed. The difference is that they have
 * a body with their implementation while pure stubs have [noImpl].
 */
private fun noImpl(): Nothing =
    throw UnsupportedOperationException("Not implemented, should not be called")

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
public fun <T> Flow<T>.observeOn(context: CoroutineContext): Flow<T> = noImpl()

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
public fun <T> Flow<T>.publishOn(context: CoroutineContext): Flow<T> = noImpl()

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
public fun <T> Flow<T>.subscribeOn(context: CoroutineContext): Flow<T> = noImpl()

/**
 * Flow analogue of `onErrorXxx` is [catch].
 * Use `catch { emitAll(fallback) }`.
 * @suppress
 */
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow analogue of 'onErrorXxx' is 'catch'. Use 'catch { emitAll(fallback) }'",
    replaceWith = ReplaceWith("catch { emitAll(fallback) }")
)
public fun <T> Flow<T>.onErrorResume(fallback: Flow<T>): Flow<T> = noImpl()

/**
 * Flow analogue of `onErrorXxx` is [catch].
 * Use `catch { emitAll(fallback) }`.
 * @suppress
 */
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow analogue of 'onErrorXxx' is 'catch'. Use 'catch { emitAll(fallback) }'",
    replaceWith = ReplaceWith("catch { emitAll(fallback) }")
)
public fun <T> Flow<T>.onErrorResumeNext(fallback: Flow<T>): Flow<T> = noImpl()

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
public fun <T> Flow<T>.subscribe(): Unit = noImpl()

/**
 * Use [launchIn] with [onEach], [onCompletion] and [catch] operators instead.
 * @suppress
 */
@Deprecated(
    message = "Use launchIn with onEach, onCompletion and catch operators instead",
    level = DeprecationLevel.ERROR
)public fun <T> Flow<T>.subscribe(onEach: suspend (T) -> Unit): Unit = noImpl()

/**
 * Use [launchIn] with [onEach], [onCompletion] and [catch] operators instead.
 * @suppress
 */
@Deprecated(
    message = "Use launchIn with onEach, onCompletion and catch operators instead",
    level = DeprecationLevel.ERROR
)public fun <T> Flow<T>.subscribe(onEach: suspend (T) -> Unit, onError: suspend (Throwable) -> Unit): Unit = noImpl()

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
public fun <T, R> Flow<T>.flatMap(mapper: suspend (T) -> Flow<R>): Flow<R> = noImpl()

/**
 * Flow analogue of `concatMap` is [flatMapConcat].
 * @suppress
 */
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow analogue of 'concatMap' is 'flatMapConcat'",
    replaceWith = ReplaceWith("flatMapConcat(mapper)")
)
public fun <T, R> Flow<T>.concatMap(mapper: (T) -> Flow<R>): Flow<R> = noImpl()

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
public fun <T> Flow<Flow<T>>.merge(): Flow<T> = noImpl()

/**
 * Flow analogue of `flatten` is [flattenConcat].
 * @suppress
 */
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow analogue of 'flatten' is 'flattenConcat'",
    replaceWith = ReplaceWith("flattenConcat()")
)
public fun <T> Flow<Flow<T>>.flatten(): Flow<T> = noImpl()

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
 * @suppress
 */
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow analogue of 'compose' is 'let'",
    replaceWith = ReplaceWith("let(transformer)")
)
public fun <T, R> Flow<T>.compose(transformer: Flow<T>.() -> Flow<R>): Flow<R> = noImpl()

/**
 * Flow analogue of `skip` is [drop].
 * @suppress
 */
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow analogue of 'skip' is 'drop'",
    replaceWith = ReplaceWith("drop(count)")
)
public fun <T> Flow<T>.skip(count: Int): Flow<T> = noImpl()

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
public fun <T> Flow<T>.forEach(action: suspend (value: T) -> Unit): Unit = noImpl()

/**
 * Flow has less verbose [scan] shortcut.
 * @suppress
 */
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow has less verbose 'scan' shortcut",
    replaceWith = ReplaceWith("scan(initial, operation)")
)
public fun <T, R> Flow<T>.scanFold(initial: R, @BuilderInference operation: suspend (accumulator: R, value: T) -> R): Flow<R> =
    noImpl()

/**
 * Flow analogue of `onErrorXxx` is [catch].
 * Use `catch { emit(fallback) }`.
 * @suppress
 */
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow analogue of 'onErrorXxx' is 'catch'. Use 'catch { emit(fallback) }'",
    replaceWith = ReplaceWith("catch { emit(fallback) }")
)
// Note: this version without predicate gives better "replaceWith" action
public fun <T> Flow<T>.onErrorReturn(fallback: T): Flow<T> = noImpl()

/**
 * Flow analogue of `onErrorXxx` is [catch].
 * Use `catch { e -> if (predicate(e)) emit(fallback) else throw e }`.
 * @suppress
 */
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

/**
 * Flow analogue of `startWith` is [onStart].
 * Use `onStart { emit(value) }`.
 * @suppress
 */
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow analogue of 'startWith' is 'onStart'. Use 'onStart { emit(value) }'",
    replaceWith = ReplaceWith("onStart { emit(value) }")
)
public fun <T> Flow<T>.startWith(value: T): Flow<T> = noImpl()

/**
 * Flow analogue of `startWith` is [onStart].
 * Use `onStart { emitAll(other) }`.
 * @suppress
 */
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow analogue of 'startWith' is 'onStart'. Use 'onStart { emitAll(other) }'",
    replaceWith = ReplaceWith("onStart { emitAll(other) }")
)
public fun <T> Flow<T>.startWith(other: Flow<T>): Flow<T> = noImpl()

/**
 * Flow analogue of `concatWith` is [onCompletion].
 * Use `onCompletion { emit(value) }`.
 * @suppress
 */
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow analogue of 'concatWith' is 'onCompletion'. Use 'onCompletion { emit(value) }'",
    replaceWith = ReplaceWith("onCompletion { emit(value) }")
)
public fun <T> Flow<T>.concatWith(value: T): Flow<T> = noImpl()

/**
 * Flow analogue of `concatWith` is [onCompletion].
 * Use `onCompletion { emitAll(other) }`.
 * @suppress
 */
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow analogue of 'concatWith' is 'onCompletion'. Use 'onCompletion { emitAll(other) }'",
    replaceWith = ReplaceWith("onCompletion { emitAll(other) }")
)
public fun <T> Flow<T>.concatWith(other: Flow<T>): Flow<T> = noImpl()

@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow analogue of 'combineLatest' is 'combine'",
    replaceWith = ReplaceWith("this.combine(other, transform)")
)
public fun <T1, T2, R> Flow<T1>.combineLatest(other: Flow<T2>, transform: suspend (T1, T2) -> R): Flow<R> =
    combine(this, other, transform)

@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow analogue of 'combineLatest' is 'combine'",
    replaceWith = ReplaceWith("combine(this, other, other2, transform)")
)
public inline fun <T1, T2, T3, R> Flow<T1>.combineLatest(
    other: Flow<T2>,
    other2: Flow<T3>,
    crossinline transform: suspend (T1, T2, T3) -> R
) = combine(this, other, other2, transform)

@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow analogue of 'combineLatest' is 'combine'",
    replaceWith = ReplaceWith("combine(this, other, other2, other3, transform)")
)
public inline fun <T1, T2, T3, T4, R> Flow<T1>.combineLatest(
    other: Flow<T2>,
    other2: Flow<T3>,
    other3: Flow<T4>,
    crossinline transform: suspend (T1, T2, T3, T4) -> R
) = combine(this, other, other2, other3, transform)

@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow analogue of 'combineLatest' is 'combine'",
    replaceWith = ReplaceWith("combine(this, other, other2, other3, transform)")
)
public inline fun <T1, T2, T3, T4, T5, R> Flow<T1>.combineLatest(
    other: Flow<T2>,
    other2: Flow<T3>,
    other3: Flow<T4>,
    other4: Flow<T5>,
    crossinline transform: suspend (T1, T2, T3, T4, T5) -> R
): Flow<R> = combine(this, other, other2, other3, other4, transform)

/**
 * Delays the emission of values from this flow for the given [timeMillis].
 * Use `onStart { delay(timeMillis) }`.
 * @suppress
 */
@Deprecated(
    level = DeprecationLevel.WARNING, // since 1.3.0, error in 1.4.0
    message = "Use 'onStart { delay(timeMillis) }'",
    replaceWith = ReplaceWith("onStart { delay(timeMillis) }")
)
public fun <T> Flow<T>.delayFlow(timeMillis: Long): Flow<T> = onStart { delay(timeMillis) }

/**
 * Delays each element emitted by the given flow for the given [timeMillis].
 * Use `onEach { delay(timeMillis) }`.
 * @suppress
 */
@Deprecated(
    level = DeprecationLevel.WARNING, // since 1.3.0, error in 1.4.0
    message = "Use 'onEach { delay(timeMillis) }'",
    replaceWith = ReplaceWith("onEach { delay(timeMillis) }")
)
public fun <T> Flow<T>.delayEach(timeMillis: Long): Flow<T> = onEach { delay(timeMillis) }

@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Flow analogues of 'switchMap' are 'transformLatest', 'flatMapLatest' and 'mapLatest'",
    replaceWith = ReplaceWith("this.flatMapLatest(transform)")
)
public fun <T, R> Flow<T>.switchMap(transform: suspend (value: T) -> Flow<R>): Flow<R> = flatMapLatest(transform)
