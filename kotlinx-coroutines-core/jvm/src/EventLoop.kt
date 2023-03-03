/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.Runnable
import kotlinx.coroutines.scheduling.*
import kotlinx.coroutines.scheduling.CoroutineScheduler

internal actual abstract class EventLoopImplPlatform: EventLoop() {
    protected abstract val thread: Thread

    protected actual fun unpark() {
        val thread = thread // atomic read
        if (Thread.currentThread() !== thread)
            unpark(thread)
    }

    protected actual open fun reschedule(now: Long, delayedTask: EventLoopImplBase.DelayedTask) {
        DefaultExecutor.schedule(now, delayedTask)
    }
}

internal class BlockingEventLoop(
    override val thread: Thread
) : EventLoopImplBase()

internal actual fun createEventLoop(): EventLoop = BlockingEventLoop(Thread.currentThread())

/**
 * Processes next event in the current thread's event loop.
 *
 * The result of this function is to be interpreted like this:
 * * `<= 0` -- there are potentially more events for immediate processing;
 * * `> 0` -- a number of nanoseconds to wait for the next scheduled event;
 * * [Long.MAX_VALUE] -- no more events or no thread-local event loop.
 *
 * Sample usage of this function:
 *
 * ```
 * while (waitingCondition) {
 *     val time = processNextEventInCurrentThread()
 *     LockSupport.parkNanos(time)
 * }
 * ```
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public fun processNextEventInCurrentThread(): Long =
    // This API is used in Ktor for serverless integration where a single thread awaits a blocking call
    // (and, to avoid actual blocking, does something via this call), see #850
    ThreadLocalEventLoop.currentOrNull()?.processNextEvent() ?: Long.MAX_VALUE

internal actual inline fun platformAutoreleasePool(crossinline block: () -> Unit) = block()

/**
 * Retrieves and executes a single task from the current system dispatcher ([Dispatchers.Default] or [Dispatchers.IO]).
 * Returns `0` if any task was executed, `>= 0` for number of nanoseconds to wait until invoking this method again
 * (implying that there will be a task to steal in N nanoseconds), `-1` if there is no tasks in the corresponding dispatcher at all.
 *
 * ### Invariants
 *
 *  - When invoked from [Dispatchers.Default] **thread** (even if the actual context is different dispatcher,
 *    [CoroutineDispatcher.limitedParallelism] or any in-place wrapper), it runs an arbitrary task that ended
 *    up being scheduled to [Dispatchers.Default] or its counterpart. Tasks scheduled to [Dispatchers.IO]
 *    **are not** executed[1].
 *  - When invoked from [Dispatchers.IO] thread, the same rules apply, but for blocking tasks only.
 *
 * [1] -- this is purely technical limitation: the scheduler does not have "notify me when CPU token is available" API,
 * and we cannot leave this method without leaving thread in its original state.
 *
 * ### Rationale
 *
 * This is an internal API that is intended to replace IDEA's core FJP decomposition.
 * The following API is provided by IDEA core:
 * ```
 * runDecomposedTaskAndJoinIt { // <- non-suspending call
 *     // spawn as many tasks as needed
 *     // these tasks can also invoke 'runDecomposedTaskAndJoinIt'
 * }
 * ```
 * The key observation here is that 'runDecomposedTaskAndJoinIt' can be invoked from `Dispatchers.Default` itself,
 * thus blocking at least one thread. To avoid deadlocks and starvation during large hierarchical decompositions,
 * 'runDecomposedTaskAndJoinIt' should not just block but also **help** execute the task or other tasks
 * until an arbitrary condition is satisfied.
 *
 * See #3439 for additional details.
 *
 * ### Limitations and caveats
 *
 * - Executes tasks in-place, thus potentially leaking irrelevant thread-locals from the current thread
 * - Is not 100% effective, because the caller should somehow "wait" (or do other work) for [Long] returned nanoseconds
 *   even when work arrives immediately after returning from this method.
 * - When there is no more work, it's up to the caller to decide what to do. It's important to remember that
 *   work to current dispatcher may arrive **later** from external sources [1]
 *
 * [1] -- this is also a technicality that can be solved in kotlinx.coroutines itself, but unfortunately requires
 *        a tremendous effort.
 *
 * @throws IllegalStateException if the current thread is not system dispatcher thread
 */
@InternalCoroutinesApi
@DelicateCoroutinesApi
@PublishedApi
internal fun runSingleTaskFromCurrentSystemDispatcher(): Long {
    val thread = Thread.currentThread()
    if (thread !is CoroutineScheduler.Worker) throw IllegalStateException("Expected CoroutineScheduler.Worker, but got $thread")
    return thread.runSingleTask()
}

/**
 * Checks whether the given thread belongs to Dispatchers.IO.
 * Note that feature "is part of the Dispatchers.IO" is *dynamic*, meaning that the thread
 * may change this status when switching between tasks.
 *
 * This function is inteded to be used on the result of `Thread.currentThread()` for diagnostic
 * purposes, and is declared as an extension only to avoid top-level scope pollution.
 */
@InternalCoroutinesApi
@DelicateCoroutinesApi
@PublishedApi
internal fun Thread.isIoDispatcherThread(): Boolean {
    if (this !is CoroutineScheduler.Worker) return false
    return isIo()
}

