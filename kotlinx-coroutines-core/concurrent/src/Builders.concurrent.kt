package kotlinx.coroutines

import kotlin.coroutines.*

/**
 * Runs a new coroutine and **blocks** the current thread until its completion.
 * This function should not be used from a coroutine. It is designed to bridge regular blocking code
 * to libraries that are written in suspending style, to be used in `main` functions and in tests.
 */
public expect fun <T> runBlocking(context: CoroutineContext = EmptyCoroutineContext, block: suspend CoroutineScope.() -> T): T