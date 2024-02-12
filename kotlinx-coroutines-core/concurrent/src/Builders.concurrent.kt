package kotlinx.coroutines

import kotlin.coroutines.*

/**
 * Runs a new coroutine and **blocks** the current thread until its completion.
 *
 * It is designed to bridge regular blocking code to libraries that are written in suspending style, to be used in
 * `main` functions and in tests.
 *
 * Calling [runBlocking] from a suspend function is redundant.
 * For example, the following code is incorrect:
 * ```
 * suspend fun loadConfiguration() {
 *     // DO NOT DO THIS:
 *     val data = runBlocking { // <- redundant and blocks the thread, do not do that
 *         fetchConfigurationData() // suspending function
 *     }
 * ```
 *
 * Here, instead of releasing the thread on which `loadConfiguration` runs if `fetchConfigurationData` suspends, it will
 * block, potentially leading to thread starvation issues.
 */
public expect fun <T> runBlocking(context: CoroutineContext = EmptyCoroutineContext, block: suspend CoroutineScope.() -> T): T
