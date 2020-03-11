/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")
@file:Suppress("UNCHECKED_CAST")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.internal.*
import kotlin.coroutines.*
import kotlin.jvm.*

// ------------------ WARNING ------------------
//   These emitting operators must use safe flow builder, because their allow
//   user code to directly emit to the underlying FlowCollector.

/**
 * Applies [transform] function to each value of the given flow.
 *
 * The receiver of the [transform] is [FlowCollector] and thus `transform` is a
 * generic function that may transform emitted element, skip it or emit it multiple times.
 *
 * This operator can be used as a building block for other operators, for example:
 *
 * ```
 * fun Flow<Int>.skipOddAndDuplicateEven(): Flow<Int> = transform { value ->
 *     if (value % 2 == 0) { // Emit only even values, but twice
 *         emit(value)
 *         emit(value)
 *     } // Do nothing if odd
 * }
 * ```
 */
@ExperimentalCoroutinesApi
public inline fun <T, R> Flow<T>.transform(
    @BuilderInference crossinline transform: suspend FlowCollector<R>.(value: T) -> Unit
): Flow<R> = flow { // Note: safe flow is used here, because collector is exposed to transform on each operation
    collect { value ->
        // kludge, without it Unit will be returned and TCE won't kick in, KT-28938
        return@collect transform(value)
    }
}

// For internal operator implementation
@PublishedApi
internal inline fun <T, R> Flow<T>.unsafeTransform(
    @BuilderInference crossinline transform: suspend FlowCollector<R>.(value: T) -> Unit
): Flow<R> = unsafeFlow { // Note: unsafe flow is used here, because unsafeTransform is only for internal use
    collect { value ->
        // kludge, without it Unit will be returned and TCE won't kick in, KT-28938
        return@collect transform(value)
    }
}

/**
 * Invokes the given [action] when the this flow starts to be collected.
 *
 * The receiver of the [action] is [FlowCollector] and thus `onStart` can emit additional elements.
 * For example:
 *
 * ```
 * flowOf("a", "b", "c")
 *     .onStart { emit("Begin") }
 *     .collect { println(it) } // prints Begin, a, b, c
 * ```
 */
@ExperimentalCoroutinesApi // tentatively stable in 1.3.0
public fun <T> Flow<T>.onStart(
    action: suspend FlowCollector<T>.() -> Unit
): Flow<T> = unsafeFlow { // Note: unsafe flow is used here, but safe collector is used to invoke start action
    val safeCollector = SafeCollector<T>(this, coroutineContext)
    try {
        safeCollector.action()
    } finally {
        safeCollector.releaseIntercepted()
    }
    collect(this) // directly delegate
}

/**
 * Invokes the given [action] when the given flow is completed or cancelled, using
 * the exception from the upstream (if any) as cause parameter of [action].
 *
 * Conceptually, `onCompletion` is similar to wrapping the flow collection into a `finally` block,
 * for example the following imperative snippet:
 *
 * ```
 * try {
 *     myFlow.collect { value ->
 *         println(value)
 *     }
 * } finally {
 *     println("Done")
 * }
 * ```
 *
 * can be replaced with a declarative one using `onCompletion`:
 *
 * ```
 * myFlow
 *     .onEach { println(it) }
 *     .onCompletion { println("Done") }
 *     .collect()
 * ```
 *
 * This operator is *transparent* to exceptions that occur in downstream flow
 * and does not observe exceptions that are thrown to cancel the flow,
 * while any exception from the [action] will be thrown downstream.
 * This behaviour can be demonstrated by the following example:
 *
 * ```
 * flow { emitData() }
 *     .map { computeOne(it) }
 *     .onCompletion { println(it) } // Can print exceptions from emitData and computeOne
 *     .map { computeTwo(it) }
 *     .onCompletion { println(it) } // Can print exceptions from emitData, computeOne, onCompletion and computeTwo
 *     .collect()
 * ```
 *
 * The receiver of the [action] is [FlowCollector] and this operator can be used to emit additional
 * elements at the end of the collection. For example:
 *
 * ```
 * flowOf("a", "b", "c")
 *     .onCompletion { emit("Done") }
 *     .collect { println(it) } // prints a, b, c, Done
 * ```
 */
@ExperimentalCoroutinesApi // tentatively stable in 1.3.0
public fun <T> Flow<T>.onCompletion(
    action: suspend FlowCollector<T>.(cause: Throwable?) -> Unit
): Flow<T> = unsafeFlow { // Note: unsafe flow is used here, but safe collector is used to invoke completion action
    val exception = try {
        catchImpl(this)
    } catch (e: Throwable) {
        /*
         * Exception from the downstream.
         * Use throwing collector to prevent any emissions from the
         * completion sequence when downstream has failed, otherwise it may
         * lead to a non-sequential behaviour impossible with `finally`
         */
        ThrowingCollector(e).invokeSafely(action, null)
        throw e
    }
    // Exception from the upstream or normal completion
    val safeCollector = SafeCollector(this, coroutineContext)
    try {
        safeCollector.invokeSafely(action, exception)
    } finally {
        safeCollector.releaseIntercepted()
    }
    exception?.let { throw it }
}

private class ThrowingCollector(private val e: Throwable) : FlowCollector<Any?> {
    override suspend fun emit(value: Any?) {
        throw e
    }
}

// It was only released in 1.3.0-M2, remove in 1.4.0
/** @suppress */
@Deprecated(level = DeprecationLevel.HIDDEN, message = "binary compatibility with a version w/o FlowCollector receiver")
public fun <T> Flow<T>.onCompletion(action: suspend (cause: Throwable?) -> Unit) =
    onCompletion { action(it) }

private suspend fun <T> FlowCollector<T>.invokeSafely(
    action: suspend FlowCollector<T>.(cause: Throwable?) -> Unit,
    cause: Throwable?
) {
    try {
        action(cause)
    } catch (e: Throwable) {
        if (cause !== null) e.addSuppressedThrowable(cause)
        throw e
    }
}
