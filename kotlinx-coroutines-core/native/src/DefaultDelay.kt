package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.native.concurrent.ObsoleteWorkersApi
import kotlin.native.concurrent.Worker

@PublishedApi
internal actual val DefaultDelay: Delay get() = DefaultDelayImpl

@OptIn(ObsoleteWorkersApi::class)
private object DefaultDelayImpl : EventLoopImplBase(), Runnable {
    init {
        incrementUseCount() // this event loop is never completed
    }

    private val _thread = atomic<Worker?>(null)

    /** Can only happen when tests close the default executor */
    override fun reschedule(now: Long, delayedTask: DelayedTask) {
        throw IllegalStateException("Attempted to schedule $delayedTask at $now after shutdown")
    }

    /**
     * All event loops are using DefaultDelay#invokeOnTimeout to avoid livelock on
     * ```
     * runBlocking(eventLoop) { withTimeout { while(isActive) { ... } } }
     * ```
     *
     * Livelock is possible only if `runBlocking` is called on internal default executed (which is used by default [delay]),
     * but it's not exposed as public API.
     */
    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle =
        scheduleInvokeOnTimeout(timeMillis, block)

    override fun run() {
        val currentThread = Worker.current
        // Identity comparisons do not work for value classes, but comparing `null` with non-null should still work
        if (!_thread.compareAndSet(null, currentThread)) return // some other thread won the race to start the thread
        ThreadLocalEventLoop.setEventLoop(DelegatingUnconfinedEventLoop)
        try {
            while (true) {
                val parkNanos = processNextEvent()
                if (parkNanos == Long.MAX_VALUE) break // no more events
                if (parkNanos > 0) currentThread.park(parkNanos / 1000L, true)
            }
        } finally {
            _thread.value = null
            ThreadLocalEventLoop.resetEventLoop()
            // recheck if queues are empty after _thread reference was set to null (!!!)
            if (!delayedQueueIsEmpty) {
                /* recreate the thread, as there is still work to do,
                and `unpark` could have awoken the thread we're currently running on */
                startThreadOrObtainSleepingThread()
            }
        }
    }

    override fun startThreadOrObtainSleepingThread(): Worker? {
        // Check if the thread is already running
        _thread.value?.let { return it }
        /* Now we know that at the moment of this call the thread was not initially running.
        This means that whatever thread is going to be running by the end of this function,
        it's going to notice the tasks it's supposed to run.
        We can return `null` unconditionally. */
        scheduleBackgroundIoTask(this)
        return null
    }

    override fun toString(): String = "DefaultDelay"
}

private object DelegatingUnconfinedEventLoop: UnconfinedEventLoop {
    override val thisLoopsTaskCanAvoidYielding: Boolean
        get() = defaultDelayRunningUnconfinedLoop()

    override val isUnconfinedLoopActive: Boolean get() = false

    override fun runUnconfinedEventLoop(initialBlock: () -> Unit) {
        ioView.dispatch(ioView, Runnable {
            ThreadLocalEventLoop.unconfinedEventLoop.runUnconfinedEventLoop(initialBlock)
        })
    }

    override fun dispatchUnconfined(task: DispatchedTask<*>) =
        defaultDelayRunningUnconfinedLoop()

    override fun tryUseAsEventLoop(): EventLoop? = null
}

private fun defaultDelayRunningUnconfinedLoop(): Nothing {
    throw UnsupportedOperationException(
        "This method can only be called from the thread where an unconfined event loop is running, " +
        "but no tasks can run on this thread."
    )
}

/** A view separate from [Dispatchers.IO].
 * [Int.MAX_VALUE] instead of `1` to avoid needlessly using the [LimitedDispatcher] machinery. */
// Without `lazy`, there is a cycle between `ioView` and `DefaultDelay` initialization, leading to a segfault:
// `ioView` attempts to create a `LimitedDispatcher`, which `by`-delegates to `DefaultDelay`,
// which is a `val` in this same file, leading to the initialization of `ioView`, forming a cycle.
private val ioView by lazy { Dispatchers.IO.limitedParallelism(Int.MAX_VALUE) }
