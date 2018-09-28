/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import java.io.*
import java.util.concurrent.*
import java.util.concurrent.locks.*

private const val SHUTDOWN_TIMEOUT = 1000L

internal inline fun withVirtualTimeSource(log: PrintStream = System.`out`, block: () -> Unit) {
    DefaultExecutor.shutdown(SHUTDOWN_TIMEOUT) // shutdown execution with old time source (in case it was working)
    val testTimeSource = VirtualTimeSource(log)
    timeSource = testTimeSource
    DefaultExecutor.ensureStarted() // should start with new time source
    try {
        block()
    } finally {
        DefaultExecutor.shutdown(SHUTDOWN_TIMEOUT)
        testTimeSource.shutdown()
        timeSource = DefaultTimeSource // restore time source
    }
}

private const val NOT_PARKED = -1L

private class ThreadStatus {
    @Volatile @JvmField
    var parkedTill = NOT_PARKED
    @Volatile @JvmField
    var permit = false
    override fun toString(): String = "parkedTill = ${TimeUnit.NANOSECONDS.toMillis(parkedTill)} ms, permit = $permit"
}

private const val MAX_WAIT_NANOS = 10_000_000_000L // 10s
private const val REAL_TIME_STEP_NANOS = 200_000_000L // 200 ms
private const val REAL_PARK_NANOS = 10_000_000L // 10 ms -- park for a little to better track real-time

@Suppress("PLATFORM_CLASS_MAPPED_TO_KOTLIN")
internal class VirtualTimeSource(
    private val log: PrintStream
) : TimeSource {
    private val mainThread: Thread = Thread.currentThread()
    private var checkpointNanos: Long = System.nanoTime()

    @Volatile
    private var isShutdown = false

    @Volatile
    private var time: Long = 0

    private var trackedTasks = 0

    private val threads = ConcurrentHashMap<Thread, ThreadStatus>()

    override fun currentTimeMillis(): Long = TimeUnit.NANOSECONDS.toMillis(time)
    override fun nanoTime(): Long = time

    override fun wrapTask(block: Runnable): Runnable {
        trackTask()
        return Runnable {
            try { block.run() }
            finally { unTrackTask() }
        }
    }

    @Synchronized
    override fun trackTask() {
        trackedTasks++
    }

    @Synchronized
    override fun unTrackTask() {
        assert(trackedTasks > 0)
        trackedTasks--
    }

    @Synchronized
    override fun registerTimeLoopThread() {
        assert(threads.putIfAbsent(Thread.currentThread(), ThreadStatus()) == null)
    }

    @Synchronized
    override fun unregisterTimeLoopThread() {
        assert(threads.remove(Thread.currentThread()) != null)
        wakeupAll()
    }

    override fun parkNanos(blocker: Any, nanos: Long) {
        if (nanos <= 0) return
        val status = threads[Thread.currentThread()]!!
        assert(status.parkedTill == NOT_PARKED)
        status.parkedTill = time + nanos.coerceAtMost(MAX_WAIT_NANOS)
        while (true) {
            checkAdvanceTime()
            if (isShutdown || time >= status.parkedTill || status.permit) {
                status.parkedTill = NOT_PARKED
                status.permit = false
                break
            }
            LockSupport.parkNanos(blocker, REAL_PARK_NANOS)
        }
    }

    override fun unpark(thread: Thread) {
        val status = threads[thread] ?: return
        status.permit = true
        LockSupport.unpark(thread)
    }

    @Synchronized
    private fun checkAdvanceTime() {
        if (isShutdown) return
        val realNanos = System.nanoTime()
        if (realNanos > checkpointNanos + REAL_TIME_STEP_NANOS) {
            checkpointNanos = realNanos
            val minParkedTill = minParkedTill()
            time = (time + REAL_TIME_STEP_NANOS).coerceAtMost(if (minParkedTill < 0) Long.MAX_VALUE else minParkedTill)
            logTime("R")
            wakeupAll()
            return
        }
        if (threads[mainThread] == null) return
        if (trackedTasks != 0) return
        val minParkedTill = minParkedTill()
        if (minParkedTill <= time) return
        time = minParkedTill
        logTime("V")
        wakeupAll()
    }

    private fun logTime(s: String) {
        log.println("[$s: Time = ${TimeUnit.NANOSECONDS.toMillis(time)} ms]")
    }

    private fun minParkedTill(): Long =
        threads.values.map { if (it.permit) NOT_PARKED else it.parkedTill }.min() ?: NOT_PARKED

    @Synchronized
    fun shutdown() {
        isShutdown = true
        wakeupAll()
        while (!threads.isEmpty()) (this as Object).wait()
    }

    private fun wakeupAll() {
        threads.keys.forEach { LockSupport.unpark(it) }
        (this as Object).notifyAll()
    }
}
