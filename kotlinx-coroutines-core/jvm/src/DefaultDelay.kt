package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlinx.coroutines.internal.*
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
            ThreadLocalEventLoop.setEventLoop(DefaultDelayImpl)
            registerTimeLoopThread()
            try {
                while (true) {
                    Thread.interrupted() // just reset interruption flag
                    val parkNanos = processNextEvent()
                    if (parkNanos == Long.MAX_VALUE) break // no more events
                    parkNanos(DefaultDelayImpl, parkNanos)
                }
            } finally {
                _thread.value = null
                unregisterTimeLoopThread()
                // recheck if queues are empty after _thread reference was set to null (!!!)
                if (isEmpty) {
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
        ioView.dispatch(ioView, this)
        return null
    }

    fun shutdownForTests(timeout: Duration) {
        if (_thread.value != null) {
            val end = System.currentTimeMillis() + timeout.inWholeMilliseconds
            while (true) {
                check(isEmpty) { "There are tasks in the DefaultExecutor" }
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

/** A view separate from [Dispatchers.IO].
 * [Int.MAX_VALUE] instead of `1` to avoid needlessly using the [LimitedDispatcher] machinery. */
private val ioView = Dispatchers.IO.limitedParallelism(Int.MAX_VALUE)
