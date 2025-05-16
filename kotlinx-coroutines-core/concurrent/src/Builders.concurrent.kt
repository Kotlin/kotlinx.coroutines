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
 * Runs the given [block] in-place in a new coroutine based on [context],
 * **blocking the current thread** until its completion, and then returning its result.
 *
 * It is designed to bridge regular blocking code to libraries that are written in suspending style, to be used in
 * `main` functions, in tests, and in non-`suspend` callbacks when `suspend` functions need to be called.
 *
 * On the JVM, if this blocked thread is interrupted (see `java.lang.Thread.interrupt`),
 * then the coroutine job is cancelled and this `runBlocking` invocation throws an `InterruptedException`.
 * On Kotlin/Native, there is no way to interrupt a thread.
 *
 * ## Structured concurrency
 *
 * The lifecycle of the new coroutine's [Job] begins with starting the [block] and completes when both the [block] and
 * all the coroutines launched in the scope complete.
 *
 * A new coroutine is created with the following properties:
 * - A new [Job] for a lexically scoped coroutine is created.
 *   Its parent is the [Job] from the [context], if any was passed.
 * - If a [ContinuationInterceptor] is passed in [context],
 *   it is used as a dispatcher of the new coroutine created by [runBlocking].
 *   Otherwise, the new coroutine is dispatched to an event loop opened on this thread.
 * - The other pieces of the context are put into the new coroutine context as is.
 * - [newCoroutineContext] is called to optionally install debugging facilities.
 *
 * The resulting context is available in the [CoroutineScope] passed as the [block]'s receiver.
 *
 * Because the new coroutine is lexically scoped, even if a [Job] was passed in the [context],
 * it will not be cancelled if [runBlocking] or some child coroutine fails with an exception.
 * Instead, the exception will be rethrown to the caller of this function.
 *
 * If any child coroutine in this scope fails with an exception,
 * the scope fails, cancelling all the other children and its own [block].
 * If children should fail independently, consider using [supervisorScope]:
 * ```
 * runBlocking(CoroutineExceptionHandler { _, e ->
 *     // handle the exception
 * }) {
 *     supervisorScope {
 *         // Children fail independently here
 *     }
 * }
 * ```
 *
 * Rephrasing this in more practical terms, the specific list of structured concurrency interactions is as follows:
 * - The caller's [currentCoroutineContext] *is not taken into account*, its cancellation does not affect [runBlocking].
 * - If the new [CoroutineScope] fails with an exception
 *   (which happens if either its [block] or any child coroutine fails with an exception),
 *   the exception is rethrown to the caller,
 *   without affecting the [Job] passed in the [context] (if any).
 *   Note that this happens on any child coroutine's failure even if [block] finishes successfully.
 * - Cancelling the [Job] passed in the [context] (if any) cancels the new coroutine and its children.
 * - [runBlocking] will only finish when all the coroutines launched in it finish.
 *   If all of them complete without failing, the [runBlocking] returns the result of the [block] to the caller.
 *
 * ## Event loop
 *
 * The default [CoroutineDispatcher] for this builder is an internal implementation of event loop that processes
 * continuations in this blocked thread until the completion of this coroutine.
 *
 * This event loop is set in a thread-local variable and is accessible to nested [runBlocking] calls and
 * coroutine tasks forming an event loop
 * (such as the tasks of [Dispatchers.Unconfined] and [MainCoroutineDispatcher.immediate]).
 *
 * Nested [runBlocking] calls may execute other coroutines' tasks instead of running their own tasks.
 *
 * When [CoroutineDispatcher] is explicitly specified in the [context], then the new coroutine runs in the context of
 * the specified dispatcher while the current thread is blocked (and possibly running tasks from other
 * [runBlocking] calls on the same thread or [Dispatchers.Unconfined]).
 *
 * See [CoroutineDispatcher] for the other implementations that are provided by `kotlinx.coroutines`.
 *
 * ## Pitfalls
 *
 * ### Calling from a suspend function
 *
 * Calling [runBlocking] from a suspend function is redundant.
 * For example, the following code is incorrect:
 * ```
 * suspend fun loadConfiguration() {
 *     // DO NOT DO THIS:
 *     val data = runBlocking { // <- redundant and blocks the thread, do not do that
 *         fetchConfigurationData() // suspending function
 *     }
 *     // ...
 * ```
 *
 * Here, instead of releasing the thread on which `loadConfiguration` runs if `fetchConfigurationData` suspends, it will
 * block, potentially leading to thread starvation issues.
 * Additionally, the [currentCoroutineContext] will be ignored, and the new computation will run in the context of
 * the new `runBlocking` coroutine.
 *
 * Instead, write it like this:
 *
 * ```
 * suspend fun loadConfiguration() {
 *     val data = fetchConfigurationData() // suspending function
 *     // ...
 * ```
 *
 * ### Sharing tasks between [runBlocking] calls
 *
 * The event loop used by [runBlocking] is shared with the other [runBlocking] calls.
 * This can lead to surprising and undesired behavior.
 *
 * ```
 * runBlocking {
 *     val job = launch {
 *         delay(50.milliseconds)
 *         println("Hello from the outer child coroutine")
 *     }
 *     runBlocking {
 *         println("Entered the inner runBlocking")
 *         delay(100.milliseconds)
 *         println("Leaving the inner runBlocking")
 *     }
 * }
 * ```
 *
 * This outputs the following:
 *
 * ```
 * Entered the inner runBlocking
 * Hello from the outer child coroutine
 * Leaving the inner runBlocking
 * ```
 *
 * For example, the following code may fail with a stack overflow error:
 *
 * ```
 * runBlocking {
 *     repeat(1000) {
 *         launch {
 *             try {
 *                 runBlocking {
 *                     // do nothing
 *                 }
 *             } catch (e: Throwable) {
 *                 println(e)
 *             }
 *         }
 *     }
 * }
 * ```
 *
 * The reason is that each new `runBlocking` attempts to run the task of the outer `runBlocking` coroutine inline,
 * but those, in turn, start new `runBlocking` calls.
 *
 * The specific behavior of work stealing may change in the future, but is unlikely to be fully fixed,
 * given how widespread [runBlocking] is.
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
