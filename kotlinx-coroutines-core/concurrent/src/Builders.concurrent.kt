@file:Suppress("LEAKED_IN_PLACE_LAMBDA", "WRONG_INVOCATION_KIND")
@file:JvmMultifileClass
@file:JvmName("BuildersKt")

package kotlinx.coroutines

import kotlin.contracts.ExperimentalContracts
import kotlin.contracts.InvocationKind
import kotlin.contracts.contract
import kotlin.coroutines.*
import kotlin.jvm.JvmMultifileClass
import kotlin.jvm.JvmName

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
 *
 * The default [CoroutineDispatcher] for this builder is an internal implementation of event loop that processes continuations
 * in this blocked thread until the completion of this coroutine.
 * See [CoroutineDispatcher] for the other implementations that are provided by `kotlinx.coroutines`.
 * If new tasks are submitted to the dispatcher created by [runBlocking] after this function returns,
 * they are resubmitted to [Dispatchers.IO].
 *
 * When [CoroutineDispatcher] is explicitly specified in the [context], then the new coroutine runs in the context of
 * the specified dispatcher while the current thread is blocked. If the specified dispatcher is an event loop of another `runBlocking`,
 * then this invocation uses the outer event loop.
 *
 * If this blocked thread is interrupted (see `Thread.interrupt`), then the coroutine job is cancelled and
 * this `runBlocking` invocation throws `InterruptedException`.
 *
 * See [newCoroutineContext][CoroutineScope.newCoroutineContext] for a description of debugging facilities that are available
 * for a newly created coroutine.
 *
 * @param context the context of the coroutine. The default value is an event loop on the current thread.
 * @param block the coroutine code.
 */
@OptIn(ExperimentalContracts::class)
@JvmName("runBlockingK")
public fun <T> runBlocking(
    context: CoroutineContext = EmptyCoroutineContext, block: suspend CoroutineScope.() -> T
): T {
    contract { callsInPlace(block, InvocationKind.EXACTLY_ONCE) }
    val contextInterceptor = context[ContinuationInterceptor]
    val eventLoop: EventLoop?
    val newContext: CoroutineContext
    if (contextInterceptor == null) {
        // create or use private event loop if no dispatcher is specified
        eventLoop = ThreadLocalEventLoop.eventLoop
        newContext = GlobalScope.newCoroutineContext(context + eventLoop)
    } else {
        eventLoop = ThreadLocalEventLoop.currentOrNull()
        newContext = GlobalScope.newCoroutineContext(context)
    }
    return runBlockingImpl(newContext, eventLoop, block)
}

/** We can't inline it, because an `expect fun` can't have contracts. */
internal expect fun <T> runBlockingImpl(
    newContext: CoroutineContext, eventLoop: EventLoop?, block: suspend CoroutineScope.() -> T
): T
