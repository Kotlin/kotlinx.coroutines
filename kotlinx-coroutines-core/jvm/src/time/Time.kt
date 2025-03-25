@file:OptIn(ExperimentalContracts::class)

package kotlinx.coroutines.time

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.selects.*
import java.time.*
import java.time.temporal.*
import kotlin.contracts.*
import kotlin.time.toKotlinDuration

/**
 * "java.time" adapter method for [kotlinx.coroutines.delay].
 */
public suspend fun delay(duration: Duration): Unit = delay(duration.toKotlinDuration())

/**
 * "java.time" adapter method for [kotlinx.coroutines.flow.debounce].
 */
@FlowPreview
public fun <T> Flow<T>.debounce(timeout: Duration): Flow<T> = debounce(timeout.toKotlinDuration())

/**
 * "java.time" adapter method for [kotlinx.coroutines.flow.sample].
 */
@FlowPreview
public fun <T> Flow<T>.sample(period: Duration): Flow<T> = sample(period.toKotlinDuration())

/**
 * "java.time" adapter method for [SelectBuilder.onTimeout].
 */
public fun <R> SelectBuilder<R>.onTimeout(duration: Duration, block: suspend () -> R): Unit =
        onTimeout(duration.toKotlinDuration(), block)

/**
 * "java.time" adapter method for [kotlinx.coroutines.withTimeout].
 */
public suspend fun <T> withTimeout(duration: Duration, block: suspend CoroutineScope.() -> T): T {
    contract {
        callsInPlace(block, InvocationKind.EXACTLY_ONCE)
    }
    return withTimeout(duration.toKotlinDuration(), block)
}

/**
 * "java.time" adapter method for [kotlinx.coroutines.withTimeoutOrNull].
 */
public suspend fun <T> withTimeoutOrNull(duration: Duration, block: suspend CoroutineScope.() -> T): T? =
    withTimeoutOrNull(duration.toKotlinDuration(), block)
