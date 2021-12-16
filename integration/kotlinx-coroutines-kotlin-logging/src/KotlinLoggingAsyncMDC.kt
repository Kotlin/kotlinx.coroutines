/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.kotlinlogging

import kotlinx.coroutines.*
import kotlinx.coroutines.slf4j.*
import mu.*

/**
 * Use a pair in an asynchronous MDC context. Example:
 * ```
 * withLoggingContextAsync("userId" to userId) {
 *   doSomething()
 * }
 * ```
 * ```
 * withLoggingContextAsync("userId" to userId, restorePrevious = false) {
 *   doSomething()
 * }
 * ```
 */
public suspend inline fun <T> withLoggingContextAsync(
    pair: Pair<String, String?>,
    restorePrevious: Boolean = true,
    crossinline body: suspend () -> T
): T = withLoggingContext(pair, restorePrevious = restorePrevious) {
    withContext(MDCContext()) {
        body()
    }
}

/**
 * Use a varying number of pairs in an asynchronous MDC context. Example:
 * ```
 * withLoggingContextAsync("userId" to userId) {
 *   doSomething()
 * }
 * ```
 */
public suspend inline fun <T> withLoggingContextAsync(
    vararg pair: Pair<String, String?>,
    restorePrevious: Boolean = true,
    crossinline body: suspend () -> T
): T = withLoggingContext(*pair, restorePrevious = restorePrevious) {
    withContext(MDCContext()) {
        body()
    }
}

/**
 * Use a map in an asynchronous MDC context. Example:
 * ```
 * withLoggingContextAsync(mapOf("userId" to userId)) {
 *   doSomething()
 * }
 * ```
 * ```
 * withLoggingContextAsync(mapOf("userId" to userId), restorePrevious = true) {
 *   doSomething()
 * }
 * ```
 */
public suspend inline fun <T> withLoggingContextAsync(
    map: Map<String, String?>,
    restorePrevious: Boolean = true,
    crossinline body: suspend () -> T
): T = withLoggingContext(map, restorePrevious = restorePrevious) {
    withContext(MDCContext()) {
        body()
    }
}
