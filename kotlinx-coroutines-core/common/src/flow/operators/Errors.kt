/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.jvm.*
import kotlinx.coroutines.flow.internal.unsafeFlow as flow

/**
 * Catches exceptions in the flow completion and calls a specified [action] with
 * the caught exception. This operator is *transparent* to exceptions that occur
 * in downstream flow and does not catch exceptions that are thrown to cancel the flow.
 *
 * For example:
 *
 * ```
 * flow { emitData() }
 *     .map { computeOne(it) }
 *     .catch { ... } // catches exceptions in emitData and computeOne
 *     .map { computeTwo(it) }
 *     .collect { process(it) } // throws exceptions from process and computeTwo
 * ```
 *
 * Conceptually, the action of `catch` operator is similar to wrapping the code of upstream flows with
 * `try { ... } catch (e: Throwable) { action(e) }`.
 *
 * Any exception in the [action] code itself proceeds downstream where it can be
 * caught by further `catch` operators if needed. If a particular exception does not need to be
 * caught it can be rethrown from the action of `catch` operator. For example:
 *
 * ```
 * flow.catch { e ->
 *     if (e !is IOException) throw e // rethrow all but IOException
 *     // e is IOException here
 *     ...
 * }
 * ```
 *
 * The [action] code has [FlowCollector] as a receiver and can [emit][FlowCollector.emit] values downstream.
 * For example, caught exception can be replaced with some wrapper value for errors:
 *
 * ```
 * flow.catch { e -> emit(ErrorWrapperValue(e)) }
 * ```
 *
 * The [action] can also use [emitAll] to fallback on some other flow in case of an error. However, to
 * retry an original flow use [retryWhen] operator that can retry the flow multiple times without
 * introducing ever-growing stack of suspending calls.
 */
public fun <T> Flow<T>.catch(action: suspend FlowCollector<T>.(cause: Throwable) -> Unit): Flow<T> =
    flow {
        val exception = catchImpl(this)
        if (exception != null) action(exception)
    }

/**
 * Retries collection of the given flow up to [retries] times when an exception that matches the
 * given [predicate] occurs in the upstream flow. This operator is *transparent* to exceptions that occur
 * in downstream flow and does not retry on exceptions that are thrown to cancel the flow.
 *
 * See [catch] for details on how exceptions are caught in flows.
 *
 * The default value of [retries] parameter is [Long.MAX_VALUE]. This value effectively means to retry forever.
 * This operator is a shorthand for the following code (see [retryWhen]). Note that `attempt` is checked first
 * and [predicate] is not called when it reaches the given number of [retries]:
 *
 * ```
 * retryWhen { cause, attempt -> attempt < retries && predicate(cause) }
 * ```
 *
 * The [predicate] parameter is always true by default. The [predicate] is a suspending function,
 * so it can be also used to introduce delay before retry, for example:
 *
 * ```
 * flow.retry(3) { e ->
 *     // retry on any IOException but also introduce delay if retrying
 *     (e is IOException).also { if (it) delay(1000) }
 * }
 * ```
 *
 * @throws IllegalArgumentException when [retries] is not positive.
 */
public fun <T> Flow<T>.retry(
    retries: Long = Long.MAX_VALUE,
    predicate: suspend (cause: Throwable) -> Boolean = { true }
): Flow<T> {
    require(retries > 0) { "Expected positive amount of retries, but had $retries" }
    return retryWhen { cause, attempt -> attempt < retries && predicate(cause) }
}

/**
 * Retries collection of the given flow when an exception occurs in the upstream flow and the
 * [predicate] returns true. The predicate also receives an `attempt` number as parameter,
 * starting from zero on the initial call. This operator is *transparent* to exceptions that occur
 * in downstream flow and does not retry on exceptions that are thrown to cancel the flow.
 *
 * For example, the following call retries the flow forever if the error is caused by `IOException`, but
 * stops after 3 retries on any other exception:
 *
 * ```
 * flow.retryWhen { cause, attempt -> cause is IOException || attempt < 3 }
 * ```
 *
 * To implement a simple retry logic with a limit on the number of retries use [retry] operator.
 *
 * Similarly to [catch] operator, the [predicate] code has [FlowCollector] as a receiver and can
 * [emit][FlowCollector.emit] values downstream.
 * The [predicate] is a suspending function, so it can be used to introduce delay before retry, for example:
 *
 * ```
 * flow.retryWhen { cause, attempt ->
 *     if (cause is IOException) {    // retry on IOException
 *         emit(RetryWrapperValue(e))
 *         delay(1000)                // delay for one second before retry
 *         true
 *     } else {                       // do not retry otherwise
 *         false
 *     }
 * }
 * ```
 *
 * See [catch] for more details.
 */
public fun <T> Flow<T>.retryWhen(predicate: suspend FlowCollector<T>.(cause: Throwable, attempt: Long) -> Boolean): Flow<T> =
    flow {
        var attempt = 0L
        var shallRetry: Boolean
        do {
            shallRetry = false
            val cause = catchImpl(this)
            if (cause != null) {
                if (predicate(cause, attempt)) {
                    shallRetry = true
                    attempt++
                } else {
                    throw cause
                }
            }
        } while (shallRetry)
    }

// Return exception from upstream or null
@Suppress("NAME_SHADOWING")
internal suspend fun <T> Flow<T>.catchImpl(
    collector: FlowCollector<T>
): Throwable? {
    var fromDownstream: Throwable? = null
    try {
        collect {
            try {
                collector.emit(it)
            } catch (e: Throwable) {
                fromDownstream = e
                throw e
            }
        }
    } catch (e: Throwable) {
        // Otherwise, smartcast is impossible
        val fromDownstream = fromDownstream
        /*
         * First check ensures that we catch an original exception, not one rethrown by an operator.
         * Seconds check ignores cancellation causes, they cannot be caught.
         */
        if (e.isSameExceptionAs(fromDownstream) || e.isCancellationCause(coroutineContext)) {
            throw e // Rethrow exceptions from downstream and cancellation causes
        } else {
            /*
             * The exception came from the upstream [semi-] independently.
             * For pure failures, when the downstream functions normally, we handle the exception as intended.
             * But if the downstream has failed prior to or concurrently
             * with the upstream, we forcefully rethrow it, preserving the contextual information and ensuring  that it's not lost.
             */
            if (fromDownstream == null) {
                return e
            }
            /*
             * We consider the upstream exception as the superseding one when both upstream and downstream
             * fail, suppressing the downstream exception, and operating similarly to `finally` block with
             * the useful addition of adding the original downstream exception to suppressed ones.
             *
             * That's important for the following scenarios:
             * ```
             * flow {
             *     val resource = ...
             *     try {
             *         ... emit as well ...
             *     } finally {
             *          resource.close() // Throws in the shutdown sequence when 'collect' already has thrown an exception
             *     }
             * }.catch { } // or retry
             * .collect { ... }
             * ```
             * when *the downstream* throws.
             */
            if (e is CancellationException) {
                fromDownstream.addSuppressed(e)
                throw fromDownstream
            } else {
                e.addSuppressed(fromDownstream)
                throw e
            }
        }
    }
    return null
}

private fun Throwable.isCancellationCause(coroutineContext: CoroutineContext): Boolean {
    val job = coroutineContext[Job]
    if (job == null || !job.isCancelled) return false
    return isSameExceptionAs(job.getCancellationException())
}

private fun Throwable.isSameExceptionAs(other: Throwable?): Boolean =
    other != null && unwrap(other) == unwrap(this)


