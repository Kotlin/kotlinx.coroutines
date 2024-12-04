@file:JvmName("DefaultExecutorKt")
package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.scheduling.*
import kotlinx.coroutines.scheduling.scheduleBackgroundIoTask
import kotlin.coroutines.*
import kotlin.time.Duration

private val defaultMainDelayOptIn = systemProp("kotlinx.coroutines.main.delay", false)

@PublishedApi
internal actual val DefaultDelay: Delay = initializeDefaultDelay()

private fun initializeDefaultDelay(): Delay {
    // Opt-out flag
    if (!defaultMainDelayOptIn) return DefaultDelayImpl
    val main = Dispatchers.Main
    /*
     * When we already are working with UI and Main threads, it makes
     * no sense to create a separate thread with timer that cannot be controller
     * by the UI runtime.
     */
    return if (main.isMissing() || main !is Delay) DefaultDelayImpl else main
}

/**
 * This method can be invoked after all coroutines are completed to wait for the default delay executor to shut down
 * in response to the lack of tasks.
 *
 * This is only useful in tests to ensure that setting a fresh virtual time source will not confuse the default delay
 * still running the previous test.
 *
 * Does nothing if the default delay executor is not in use.
 *
 * @throws IllegalStateException if the shutdown process notices new tasks entering the system
 * @throws IllegalStateException if the shutdown process times out
 */
internal fun ensureDefaultDelayDeinitialized(timeout: Duration) {
    (DefaultDelay as? DefaultDelayImpl)?.shutdownForTests(timeout)
}

private object DefaultDelayImpl : EventLoopImplBase(), Runnable {
    const val THREAD_NAME = "kotlinx.coroutines.DefaultDelay"

    init {
        incrementUseCount() // this event loop is never completed
    }

    private val _thread = atomic<Thread?>(null)

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
        val currentThread = Thread.currentThread()
        if (!_thread.compareAndSet(null, currentThread)) return // some other thread won the race to start the thread
        val oldName = currentThread.name
        currentThread.name = THREAD_NAME
        try {
            ThreadLocalEventLoop.setEventLoop(DelegatingUnconfinedEventLoop)
            registerTimeLoopThread()
            unTrackTask(this) /** see the comment in [startThreadOrObtainSleepingThread] */
            try {
                while (true) {
                    Thread.interrupted() // just reset interruption flag
                    val parkNanos = processNextEvent()
                    if (parkNanos == Long.MAX_VALUE) break // no more events
                    if (parkNanos > 0) parkNanos(this@DefaultDelayImpl, parkNanos)
                }
            } finally {
                _thread.value = null
                unregisterTimeLoopThread()
                ThreadLocalEventLoop.resetEventLoop()
                // recheck if queues are empty after _thread reference was set to null (!!!)
                if (delayedQueueIsEmpty) {
                    notifyAboutThreadExiting()
                } else {
                    /* recreate the thread, as there is still work to do,
                    and `unpark` could have awoken the thread we're currently running on */
                    startThreadOrObtainSleepingThread()
                }
            }
        } finally {
            currentThread.name = oldName
        }
    }

    override fun startThreadOrObtainSleepingThread(): Thread? {
        // Check if the thread is already running
        _thread.value?.let { return it }
        /* Now we know that at the moment of this call the thread was not initially running.
        This means that whatever thread is going to be running by the end of this function,
        it's going to notice the tasks it's supposed to run.
        We can return `null` unconditionally. */
        /** If this function is called from a thread that's already registered as a time loop thread,
        because a time loop thread is not parked right now, the time source will not advance time *currently*,
        but it may do that as soon as the thread calling this is parked, which may happen earlier than the default
        delay thread has a chance to run.
        Because of that, we notify the time source that something is actually happening right now.
        This would work automatically if instead of [scheduleBackgroundIoTask] we used [CoroutineDispatcher.dispatch] on
        [Dispatchers.IO], but then, none of the delays would be skipped, as the whole time a [DefaultDelay] thread runs
        would be considered as a task.
        Therefore, we register a task right now and mark it as completed as soon as a [DefaultDelay] time loop gets
        registered. */
        trackTask(this)
        scheduleBackgroundIoTask(this)
        return null
    }

    fun shutdownForTests(timeout: Duration) {
        if (_thread.value != null) {
            val end = System.currentTimeMillis() + timeout.inWholeMilliseconds
            while (true) {
                synchronized(this) {
                    unpark(_thread.value ?: return)
                    val toWait = end - System.currentTimeMillis()
                    check(toWait > 0) { "Timeout waiting for DefaultExecutor to shutdown" }
                    (this as Object).wait(toWait)
                }
            }
        }
    }

    private fun notifyAboutThreadExiting() {
        synchronized(this) { (this as Object).notifyAll() }
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
private val ioView = Dispatchers.IO.limitedParallelism(Int.MAX_VALUE)
