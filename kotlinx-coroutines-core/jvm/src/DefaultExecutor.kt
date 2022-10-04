/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import java.util.concurrent.*
import kotlin.coroutines.*

private val defaultMainDelayOptIn = systemProp("kotlinx.coroutines.main.delay", false)

internal actual val DefaultDelay: Delay = initializeDefaultDelay()

private fun initializeDefaultDelay(): Delay {
    // Opt-out flag
    if (!defaultMainDelayOptIn) return DefaultExecutor
    val main = Dispatchers.Main
    /*
     * When we already are working with UI and Main threads, it makes
     * no sense to create a separate thread with timer that cannot be controller
     * by the UI runtime.
     */
    return if (main.isMissing() || main !is Delay) DefaultExecutor else main
}

@Suppress("PLATFORM_CLASS_MAPPED_TO_KOTLIN")
internal actual object DefaultExecutor : EventLoopImplBase(), Runnable {
    const val THREAD_NAME = "kotlinx.coroutines.DefaultExecutor"

    init {
        incrementUseCount() // this event loop is never completed
    }

    private const val DEFAULT_KEEP_ALIVE_MS = 1000L // in milliseconds

    private val KEEP_ALIVE_NANOS = TimeUnit.MILLISECONDS.toNanos(
        try {
            java.lang.Long.getLong("kotlinx.coroutines.DefaultExecutor.keepAlive", DEFAULT_KEEP_ALIVE_MS)
        } catch (e: SecurityException) {
            DEFAULT_KEEP_ALIVE_MS
        })

    @Suppress("ObjectPropertyName")
    @Volatile
    private var _thread: Thread? = null

    override val thread: Thread
        get() = _thread ?: createThreadSync()

    private const val FRESH = 0
    private const val ACTIVE = 1
    private const val SHUTDOWN_REQ = 2
    private const val SHUTDOWN_ACK = 3
    private const val SHUTDOWN = 4

    @Volatile
    private var debugStatus: Int = FRESH

    private val isShutDown: Boolean get() = debugStatus == SHUTDOWN

    private val isShutdownRequested: Boolean get() {
        val debugStatus = debugStatus
        return debugStatus == SHUTDOWN_REQ || debugStatus == SHUTDOWN_ACK
    }

    actual override fun enqueue(task: Runnable) {
        if (isShutDown) shutdownError()
        super.enqueue(task)
    }

     override fun reschedule(now: Long, delayedTask: DelayedTask) {
         // Reschedule on default executor can only be invoked after Dispatchers.shutdown
         shutdownError()
    }

    private fun shutdownError() {
        throw RejectedExecutionException("DefaultExecutor was shut down. " +
            "This error indicates that Dispatchers.shutdown() was invoked prior to completion of exiting coroutines, leaving coroutines in incomplete state. " +
            "Please refer to Dispatchers.shutdown documentation for more details")
    }

    override fun shutdown() {
        debugStatus = SHUTDOWN
        super.shutdown()
    }

    /**
     * All event loops are using DefaultExecutor#invokeOnTimeout to avoid livelock on
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
        ThreadLocalEventLoop.setEventLoop(this)
        registerTimeLoopThread()
        try {
            var shutdownNanos = Long.MAX_VALUE
            if (!notifyStartup()) return
            while (true) {
                Thread.interrupted() // just reset interruption flag
                var parkNanos = processNextEvent()
                if (parkNanos == Long.MAX_VALUE) {
                    // nothing to do, initialize shutdown timeout
                    val now = nanoTime()
                    if (shutdownNanos == Long.MAX_VALUE) shutdownNanos = now + KEEP_ALIVE_NANOS
                    val tillShutdown = shutdownNanos - now
                    if (tillShutdown <= 0) return // shut thread down
                    parkNanos = parkNanos.coerceAtMost(tillShutdown)
                } else
                    shutdownNanos = Long.MAX_VALUE
                if (parkNanos > 0) {
                    // check if shutdown was requested and bail out in this case
                    if (isShutdownRequested) return
                    parkNanos(this, parkNanos)
                }
            }
        } finally {
            _thread = null // this thread is dead
            acknowledgeShutdownIfNeeded()
            unregisterTimeLoopThread()
            // recheck if queues are empty after _thread reference was set to null (!!!)
            if (!isEmpty) thread // recreate thread if it is needed
        }
    }

    @Synchronized
    private fun createThreadSync(): Thread {
        return _thread ?: Thread(this, THREAD_NAME).apply {
            _thread = this
            isDaemon = true
            start()
        }
    }

    // used for tests
    @Synchronized
    internal fun ensureStarted() {
        assert { _thread == null } // ensure we are at a clean state
        assert { debugStatus == FRESH || debugStatus == SHUTDOWN_ACK }
        debugStatus = FRESH
        createThreadSync() // create fresh thread
        while (debugStatus == FRESH) (this as Object).wait()
    }

    @Synchronized
    private fun notifyStartup(): Boolean {
        if (isShutdownRequested) return false
        debugStatus = ACTIVE
        (this as Object).notifyAll()
        return true
    }

    @Synchronized // used _only_ for tests
    fun shutdownForTests(timeout: Long) {
        val deadline = System.currentTimeMillis() + timeout
        if (!isShutdownRequested) debugStatus = SHUTDOWN_REQ
        // loop while there is anything to do immediately or deadline passes
        while (debugStatus != SHUTDOWN_ACK && _thread != null) {
            _thread?.let { unpark(it) } // wake up thread if present
            val remaining = deadline - System.currentTimeMillis()
            if (remaining <= 0) break
            (this as Object).wait(timeout)
        }
        // restore fresh status
        debugStatus = FRESH
    }

    @Synchronized
    private fun acknowledgeShutdownIfNeeded() {
        if (!isShutdownRequested) return
        debugStatus = SHUTDOWN_ACK
        resetAll() // clear queues
        (this as Object).notifyAll()
    }

    internal val isThreadPresent
        get() = _thread != null
}
