/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.jvm.*
import kotlinx.coroutines.flow.unsafeFlow as flow

// TODO discuss usability from IDE with lambda as last parameter
public typealias ExceptionPredicate = (Throwable) -> Boolean

private val ALWAYS_TRUE: ExceptionPredicate = { true }

/**
 * Switches to the [fallback] flow if the original flow throws an exception that matches the [predicate].
 */
@FlowPreview
public fun <T> Flow<T>.onErrorCollect(
    fallback: Flow<T>,
    predicate: ExceptionPredicate = ALWAYS_TRUE
): Flow<T> = collectSafely { e ->
    if (!predicate(e)) throw e
    fallback.collect { value ->
        emit(value)
    }
}

/**
 * Emits the [fallback] value and finishes successfully if the original flow throws exception that matches the given [predicate];
 */
@FlowPreview
public fun <T> Flow<T>.onErrorReturn(fallback: T, predicate: ExceptionPredicate = ALWAYS_TRUE): Flow<T> =
    collectSafely { e ->
        if (!predicate(e)) throw e
        emit(fallback)
    }

/**
 * Operator that retries [n][retries] times to collect the given flow in an exception that matches the given [predicate] occurs
 * in the given flow. Exceptions from collectors of this flow are not retried.
 */
@FlowPreview
public fun <T> Flow<T>.retry(
    retries: Int = Int.MAX_VALUE,
    predicate: ExceptionPredicate = ALWAYS_TRUE
): Flow<T> {
    require(retries > 0) { "Expected positive amount of retries, but had $retries" }
    return flow {
        @Suppress("NAME_SHADOWING")
        var retries = retries
        // Note that exception may come from the downstream operators, we should not switch on that
        while (true) {
            var fromDownstream = false
            try {
                collect { value ->
                    try {
                        emit(value)
                    } catch (e: Throwable) {
                        fromDownstream = true
                        throw e
                    }
                }
                break
            } catch (e: Throwable) {
                if (fromDownstream) throw e
                if (!predicate(e) || retries-- == 0) throw e
            }
        }
    }
}

private fun <T> Flow<T>.collectSafely(onException: suspend FlowCollector<in T>.(Throwable) -> Unit): Flow<T> =
    flow {
        // Note that exception may come from the downstream operators, we should not switch on that
        var fromDownstream = false
        try {
            collect {
                try {
                    emit(it)
                } catch (e: Throwable) {
                    fromDownstream = true
                    throw e
                }
            }
        } catch (e: Throwable) {
            if (fromDownstream) throw e
            onException(e)
        }
    }
