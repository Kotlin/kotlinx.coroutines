/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.jvm.*

internal class VirtualTimeDispatcher(enclosingScope: CoroutineScope) : CoroutineDispatcher(), Delay {
    private val originalDispatcher = enclosingScope.coroutineContext[ContinuationInterceptor] as CoroutineDispatcher
    private val heap = ArrayList<TimedTask>() // TODO use MPP heap/ordered set implementation (commonize ThreadSafeHeap)

    var currentTime = 0L
        private set

    init {
        /*
         * Launch "event-loop-owning" task on start of the virtual time event loop.
         * It ensures the progress of the enclosing event-loop and polls the timed queue
         * when the enclosing event loop is empty, emulating virtual time.
         */
        enclosingScope.launch {
            while (true) {
                val delayNanos = ThreadLocalEventLoop.currentOrNull()?.processNextEvent()
                    ?: error("Event loop is missing, virtual time source works only as part of event loop")
                if (delayNanos <= 0) continue
                if (delayNanos > 0 && delayNanos != Long.MAX_VALUE) error("Unexpected external delay: $delayNanos")
                val nextTask = heap.minBy { it.deadline } ?: return@launch
                heap.remove(nextTask)
                currentTime = nextTask.deadline
                nextTask.run()
            }
        }
    }

    private inner class TimedTask(
        private val runnable: Runnable,
        @JvmField val deadline: Long
    ) : DisposableHandle, Runnable by runnable {

        override fun dispose() {
            heap.remove(this)
        }
    }

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        originalDispatcher.dispatch(context, block)
    }

    @ExperimentalCoroutinesApi
    override fun isDispatchNeeded(context: CoroutineContext): Boolean = originalDispatcher.isDispatchNeeded(context)

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle {
        val task = TimedTask(block, deadline(timeMillis))
        heap += task
        return task
    }

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        val task = TimedTask(Runnable { with(continuation) { resumeUndispatched(Unit) } }, deadline(timeMillis))
        heap += task
        continuation.invokeOnCancellation { task.dispose() }
    }

    private fun deadline(timeMillis: Long) =
        if (timeMillis == Long.MAX_VALUE) Long.MAX_VALUE else currentTime + timeMillis
}

/**
 * Runs a test ([TestBase.runTest]) with a virtual time source.
 * This runner has the following constraints:
 * 1) It works only in the event-loop environment and it is relying on it.
 *    None of the coroutines should be launched in any dispatcher different from a current
 * 2) Regular tasks always dominate delayed ones. It means that
 *    `launch { while(true) yield() }` will block the progress of the delayed tasks
 * 3) [TestBase.finish] should always be invoked.
 *    Given all the constraints into account, it is easy to mess up with a test and actually
 *    return from [withVirtualTime] before the test is executed completely.
 *    To decrease the probability of such error, additional `finish` constraint is added.
 */
public fun TestBase.withVirtualTime(block: suspend CoroutineScope.() -> Unit) = runTest {
    withContext(Dispatchers.Unconfined) {
        // Create a platform-independent event loop
        val dispatcher = VirtualTimeDispatcher(this)
        withContext(dispatcher) { block() }
        ensureFinished()
    }
}
