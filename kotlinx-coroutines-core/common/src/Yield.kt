package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.intrinsics.*

/**
 * Suspends this coroutine and immediately schedules it for further execution.
 *
 * A coroutine runs uninterrupted on a thread until the coroutine suspends,
 * giving other coroutines a chance to use that thread for their computations.
 * Normally, coroutines suspend whenever they wait for something to happen:
 * for example, trying to receive a value from a channel that's currently empty will suspend.
 * Sometimes, a coroutine does not need to wait for anything,
 * but we still want it to give other coroutines a chance to run.
 * Calling [yield] has this effect:
 *
 * ```
 * fun updateProgressBar(value: Int, marker: String) {
 *     print(marker)
 * }
 * val singleThreadedDispatcher = Dispatchers.Default.limitedParallelism(1)
 * withContext(singleThreadedDispatcher) {
 *     launch {
 *         repeat(5) {
 *             updateProgressBar(it, "A")
 *             yield()
 *         }
 *     }
 *     launch {
 *         repeat(5) {
 *             updateProgressBar(it, "B")
 *             yield()
 *         }
 *     }
 * }
 * ```
 *
 * In this example, without the [yield], first, `A` would run its five stages of work to completion, and only then
 * would `B` even start executing.
 * With both `yield` calls, the coroutines share the single thread with each other after each stage of work.
 * This is useful when several coroutines running on the same thread (or thread pool) must regularly publish
 * their results for the program to stay responsive.
 * 
 * This suspending function is cancellable: if the [Job] of the current coroutine is cancelled while
 * [yield] is invoked or while waiting for dispatch, it immediately resumes with [CancellationException].
 * There is a **prompt cancellation guarantee**: even if this function is ready to return the result, but was cancelled
 * while suspended, [CancellationException] will be thrown. See [suspendCancellableCoroutine] for low-level details.
 *
 * **Note**: if there is only a single coroutine executing on the current dispatcher,
 * it is possible that [yield] will not actually suspend.
 * However, even in that case, the [check for cancellation][ensureActive] still happens.
 *
 * **Note**: if there is no [CoroutineDispatcher] in the context, it does not suspend.
 *
 * ## Pitfall: using `yield` to wait for something to happen
 *
 * Using `yield` for anything except a way to ensure responsiveness is often a problem.
 * When possible, it is recommended to structure the code in terms of coroutines waiting for some events instead of
 * yielding.
 * Below, we list the common problems involving [yield] and outline how to avoid them.
 *
 * ### Case 1: using `yield` to ensure a specific interleaving of actions
 *
 * ```
 * val singleThreadedDispatcher = Dispatchers.Default.limitedParallelism(1)
 * withContext(singleThreadedDispatcher) {
 *     var value: Int? = null
 *     val job = launch { // a new coroutine on the same dispatcher
 *         // yield() // uncomment to see the crash
 *         value = 42
 *         println("2. Value provided")
 *     }
 *     check(value == null)
 *     println("No value yet!")
 *     println("1. Awaiting the value...")
 *     // ANTIPATTERN! DO NOT WRITE SUCH CODE!
 *     yield() // allow the other coroutine to run
 *     // job.join() // would work more reliably in this scenario!
 *     check(value != null)
 *     println("3. Obtained $value")
 * }
 * ```
 *
 * Here, [yield] allows `singleThreadedDispatcher` to execute the task that ultimately provides the `value`.
 * Without the [yield], the `value != null` check would be executed directly after `Awaiting the value` is printed.
 * However, if the value-producing coroutine is modified to suspend before providing the value, this will
 * no longer work; explicitly waiting for the coroutine to finish via [Job.join] instead is robust against such changes.
 *
 * Therefore, it is an antipattern to use `yield` to synchronize code across several coroutines.
 *
 * ### Case 2: using `yield` in a loop to wait for something to happen
 *
 * ```
 * val singleThreadedDispatcher = Dispatchers.Default.limitedParallelism(1)
 * withContext(singleThreadedDispatcher) {
 *     var value: Int? = null
 *     val job = launch { // a new coroutine on the same dispatcher
 *         delay(1.seconds)
 *         value = 42
 *     }
 *     // ANTIPATTERN! DO NOT WRITE SUCH CODE!
 *     while (value == null) {
 *         yield() // allow the other coroutines to run
 *     }
 *     println("Obtained $value")
 * }
 * ```
 *
 * This example will lead to correct results no matter how much the value-producing coroutine suspends,
 * but it is still flawed.
 * For the one second that it takes for the other coroutine to obtain the value,
 * `value == null` would be constantly re-checked, leading to unjustified resource consumption.
 *
 * In this specific case, [CompletableDeferred] can be used instead:
 *
 * ```
 * val singleThreadedDispatcher = Dispatchers.Default.limitedParallelism(1)
 * withContext(singleThreadedDispatcher) {
 *     val deferred = CompletableDeferred<Int>()
 *     val job = launch { // a new coroutine on the same dispatcher
 *         delay(1.seconds)
 *         deferred.complete(42)
 *     }
 *     val value = deferred.await()
 *     println("Obtained $value")
 * }
 * ```
 *
 * `while (channel.isEmpty) { yield() }; channel.receive()` can be replaced with just `channel.receive()`;
 * `while (job.isActive) { yield() }` can be replaced with [`job.join()`][Job.join];
 * in both cases, this will avoid the unnecessary work of checking the loop conditions.
 * In general, seek ways to allow a coroutine to stay suspended until it actually has useful work to do.
 *
 * ## Implementation details
 *
 * Some coroutine dispatchers include optimizations that make yielding different from normal suspensions.
 * For example, when yielding, [Dispatchers.Unconfined] checks whether there are any other coroutines in the event
 * loop where the current coroutine executes; if not, the sole coroutine continues to execute without suspending.
 * Also, `Dispatchers.IO` and `Dispatchers.Default` on the JVM tweak the scheduling behavior to improve liveness
 * when `yield()` is used in a loop.
 *
 * For custom implementations of [CoroutineDispatcher], this function checks [CoroutineDispatcher.isDispatchNeeded] and
 * then invokes [CoroutineDispatcher.dispatch] regardless of the result; no way is provided to change this behavior.
 */
public suspend fun yield(): Unit = suspendCoroutineUninterceptedOrReturn sc@ { uCont ->
    val context = uCont.context
    context.ensureActive()
    val cont = uCont.intercepted() as? DispatchedContinuation<Unit> ?: return@sc Unit
    if (cont.dispatcher.safeIsDispatchNeeded(context)) {
        // this is a regular dispatcher -- do simple dispatchYield
        cont.dispatchYield(context, Unit)
    } else {
        // This is either an "immediate" dispatcher or the Unconfined dispatcher
        // This code detects the Unconfined dispatcher even if it was wrapped into another dispatcher
        val yieldContext = YieldContext()
        cont.dispatchYield(context + yieldContext, Unit)
        // Special case for the unconfined dispatcher that can yield only in existing unconfined loop
        if (yieldContext.dispatcherWasUnconfined) {
            // Means that the Unconfined dispatcher got the call, but did not do anything.
            // See also code of "Unconfined.dispatch" function.
            return@sc if (cont.yieldUndispatched()) COROUTINE_SUSPENDED else Unit
        }
        // Otherwise, it was some other dispatcher that successfully dispatched the coroutine
    }
    COROUTINE_SUSPENDED
}
