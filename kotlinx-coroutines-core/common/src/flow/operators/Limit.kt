/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */


@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.flow.unsafeFlow as flow
import kotlinx.coroutines.*
import kotlin.jvm.*

/**
 * Returns a flow that ignores first [count] elements.
 */
@FlowPreview
public fun <T> Flow<T>.drop(count: Int): Flow<T> {
    require(count >= 0) { "Drop count should be non-negative, but had $count" }
    return flow {
        var skipped = 0
        collect { value ->
            if (++skipped > count) emit(value)
        }
    }
}

/**
 * Returns a flow containing all elements except first elements that satisfy the given predicate.
 */
@FlowPreview
public fun <T> Flow<T>.dropWhile(predicate: suspend (T) -> Boolean): Flow<T> = flow {
    var matched = false
    collect { value ->
        if (matched) {
            emit(value)
        } else if (!predicate(value)) {
            matched = true
            emit(value)
        }
    }
}

/**
 * Returns a flow that contains first [count] elements.
 * When [count] elements are consumed, the original flow is cancelled.
 */
@FlowPreview
public fun <T> Flow<T>.take(count: Int): Flow<T> {
    require(count > 0) { "Take count should be positive, but had $count" }
    return flow {
        var consumed = 0
        try {
            collect { value ->
                emit(value)
                if (++consumed == count) {
                    throw TakeLimitException()
                }
            }
        } catch (e: TakeLimitException) {
            // Nothing, bail out
        }
    }
}

/**
 * Returns a flow that contains first elements satisfying the given [predicate].
 */
@FlowPreview
public fun <T> Flow<T>.takeWhile(predicate: suspend (T) -> Boolean): Flow<T> = flow {
    try {
        collect { value ->
            if (predicate(value)) emit(value)
            else throw TakeLimitException()
        }
    } catch (e: TakeLimitException) {
        // Nothing, bail out
    }
}

private class TakeLimitException : CancellationException("Flow limit is reached, cancelling") {
    // TODO expect/actual
    // override fun fillInStackTrace(): Throwable = this
}
