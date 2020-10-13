/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")
@file:Suppress("UNCHECKED_CAST")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.internal.*
import kotlin.jvm.*

// ------------------ WARNING ------------------
//   These emitting operators must use safe flow builder, because they allow
//   user code to directly emit to the underlying FlowCollector.

/**
 * Applies [transform] function to each value of the given flow.
 *
 * The receiver of the `transform` is [FlowCollector] and thus `transform` is a
 * flexible function that may transform emitted element, skip it or emit it multiple times.
 *
 * This operator generalizes [filter] and [map] operators and
 * can be used as a building block for other operators, for example:
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
 * Returns a flow that invokes the given [action] **before** this flow starts to be collected.
 *
 * The [action] is called before the upstream flow is started, so if it is used with a [SharedFlow]
 * there is **no guarantee** that emissions from the upstream flow that happen inside or immediately
 * after this `onStart` action will be collected
 * (see [onSubscription] for an alternative operator on shared flows).
 *
 * The receiver of the [action] is [FlowCollector], so `onStart` can emit additional elements.
 * For example:
 *
 * ```
 * flowOf("a", "b", "c")
 *     .onStart { emit("Begin") }
 *     .collect { println(it) } // prints Begin, a, b, c
 * ```
 */
@ExperimentalCoroutinesApi
public fun <T> Flow<T>.onStart(
    action: suspend FlowCollector<T>.() -> Unit
): Flow<T> = unsafeFlow { // Note: unsafe flow is used here, but safe collector is used to invoke start action
    val safeCollector = SafeCollector<T>(this, currentCoroutineContext())
    try {
        safeCollector.action()
    } finally {
        safeCollector.releaseIntercepted()
    }
    collect(this) // directly delegate
}

/**
 * Returns a flow that invokes the given [action] **after** the flow is completed or cancelled, passing
 * the cancellation exception or failure as cause parameter of [action].
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
 * Unlike [catch], this operator reports exception that occur both upstream and downstream
 * and observe exceptions that are thrown to cancel the flow. Exception is empty if and only if
 * the flow had fully completed successfully. Conceptually, the following code:
 *
 * ```
 * myFlow.collect { value ->
 *     println(value)
 * }
 * println("Completed successfully")
 * ```
 *
 * can be replaced with:
 *
 * ```
 * myFlow
 *     .onEach { println(it) }
 *     .onCompletion { if (it == null) println("Completed successfully") }
 *     .collect()
 * ```
 *
 * The receiver of the [action] is [FlowCollector] and this operator can be used to emit additional
 * elements at the end **if it completed successfully**. For example:
 *
 * ```
 * flowOf("a", "b", "c")
 *     .onCompletion { emit("Done") }
 *     .collect { println(it) } // prints a, b, c, Done
 * ```
 *
 * In case of failure or cancellation, any attempt to emit additional elements throws the corresponding exception.
 * Use [catch] if you need to suppress failure and replace it with emission of elements.
 */
@ExperimentalCoroutinesApi
public fun <T> Flow<T>.onCompletion(
    action: suspend FlowCollector<T>.(cause: Throwable?) -> Unit
): Flow<T> = unsafeFlow { // Note: unsafe flow is used here, but safe collector is used to invoke completion action
    try {
        collect(this)
    } catch (e: Throwable) {
        /*
         * Use throwing collector to prevent any emissions from the
         * completion sequence when downstream has failed, otherwise it may
         * lead to a non-sequential behaviour impossible with `finally`
         */
        ThrowingCollector(e).invokeSafely(action, e)
        throw e
    }
    // Normal completion
    SafeCollector(this, currentCoroutineContext()).invokeSafely(action, null)
}

/**
 * Invokes the given [action] when this flow completes without emitting any elements.
 * The receiver of the [action] is [FlowCollector], so `onEmpty` can emit additional elements.
 * For example:
 *
 * ```
 * emptyFlow<Int>().onEmpty {
 *     emit(1)
 *     emit(2)
 * }.collect { println(it) } // prints 1, 2
 * ```
 */
@ExperimentalCoroutinesApi
public fun <T> Flow<T>.onEmpty(
    action: suspend FlowCollector<T>.() -> Unit
): Flow<T> = unsafeFlow {
    var isEmpty = true
    collect {
        isEmpty = false
        emit(it)
    }
    if (isEmpty) {
        val collector = SafeCollector(this, currentCoroutineContext())
        try {
            collector.action()
        } finally {
            collector.releaseIntercepted()
        }
    }
}

private class ThrowingCollector(private val e: Throwable) : FlowCollector<Any?> {
    override suspend fun emit(value: Any?) {
        throw e
    }
}

// It was only released in 1.3.0-M2, remove in 1.4.0
/** @suppress */
@Deprecated(level = DeprecationLevel.HIDDEN, message = "binary compatibility with a version w/o FlowCollector receiver")
public fun <T> Flow<T>.onCompletion(action: suspend (cause: Throwable?) -> Unit): Flow<T> =
    onCompletion { action(it) }

private suspend fun <T> FlowCollector<T>.invokeSafely(
    action: suspend FlowCollector<T>.(cause: Throwable?) -> Unit,
    cause: Throwable?
) {
    try {
        action(cause)
    } catch (e: Throwable) {
        if (cause !== null && cause !== e) e.addSuppressedThrowable(cause)
        throw e
    }
}
