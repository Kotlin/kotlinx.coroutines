package kotlinx.coroutines

import kotlinx.atomicfu.atomic
import kotlinx.coroutines.internal.ThreadSafeHeap
import kotlinx.coroutines.internal.ThreadSafeHeapNode
import kotlinx.coroutines.testing.*
import kotlin.coroutines.*
import kotlin.jvm.*
import kotlin.time.*
import kotlin.time.Duration.Companion.nanoseconds

internal class VirtualTimeDispatcher(enclosingScope: CoroutineScope) : CoroutineDispatcher(), Delay {
    private val originalDispatcher = enclosingScope.coroutineContext[ContinuationInterceptor] as CoroutineDispatcher
    private val heap = ThreadSafeHeap<TimedTask>()

    /** This counter establishes some order on the events that happen at the same virtual time. */
    private val count = atomic(0)

    private val timeSource = TestTimeSource()

    val currentTime: ComparableTimeMark
        get() = timeSource.markNow()

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
                if (delayNanos > 0 && delayNanos != Long.MAX_VALUE) {
                    if (usesSharedEventLoop) {
                        val targetTime = currentTime + delayNanos.nanoseconds
                        while (currentTime < targetTime) {
                            val nextTask = heap.removeFirstIf { it.deadline <= targetTime } ?: break
                            timeSource += nextTask.deadline - currentTime
                            nextTask.run()
                        }
                        if (targetTime > currentTime) timeSource += targetTime - currentTime
                    } else {
                        error("Unexpected external delay: $delayNanos")
                    }
                }
                val nextTask = heap.removeFirstOrNull() ?: return@launch
                heap.remove(nextTask)
                timeSource += nextTask.deadline - currentTime
                nextTask.run()
            }
        }
    }

    private inner class TimedTask(
        private val runnable: Runnable,
        val deadline: ComparableTimeMark,
        @JvmField val count: Int,
    ) : DisposableHandle, Runnable by runnable, Comparable<TimedTask>, ThreadSafeHeapNode {
        override var heap: ThreadSafeHeap<*>? = null
        override var index: Int = 0

        override fun compareTo(other: TimedTask): Int =
            compareValuesBy(this, other, TimedTask::deadline, TimedTask::count)

        override fun dispose() {
            this@VirtualTimeDispatcher.heap.remove(this)
        }
    }

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        originalDispatcher.dispatch(context, block)
    }

    override fun isDispatchNeeded(context: CoroutineContext): Boolean = originalDispatcher.isDispatchNeeded(context)

    override fun invokeOnTimeout(timeout: Duration, block: Runnable, context: CoroutineContext): DisposableHandle =
        schedule(timeout, block)

    override fun scheduleResumeAfterDelay(time: Duration, continuation: CancellableContinuation<Unit>) {
        schedule(time, Runnable {
            with(continuation) { resumeUndispatched(Unit) }
        }).also { continuation.disposeOnCancellation(it) }
    }

    private fun schedule(time: Duration, block: Runnable): DisposableHandle =
        TimedTask(block, currentTime + time, count.getAndIncrement()).also { heap.addLast(it) }

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
        checkFinishCall(allowNotUsingExpect = false)
    }
}
