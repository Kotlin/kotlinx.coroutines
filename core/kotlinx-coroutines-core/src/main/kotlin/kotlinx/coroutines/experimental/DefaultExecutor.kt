/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental

import java.util.concurrent.*

@Suppress("PLATFORM_CLASS_MAPPED_TO_KOTLIN")
internal object DefaultExecutor : EventLoopBase(), Runnable {

    override val isCompleted: Boolean get() = false

    private const val DEFAULT_KEEP_ALIVE = 1000L // in milliseconds

    private val KEEP_ALIVE_NANOS = TimeUnit.MILLISECONDS.toNanos(
        try {
            java.lang.Long.getLong("kotlinx.coroutines.DefaultExecutor.keepAlive", DEFAULT_KEEP_ALIVE)
        } catch (e: SecurityException) {
            DEFAULT_KEEP_ALIVE
        })

    @Volatile
    private var _thread: Thread? = null

    private const val FRESH = 0
    private const val ACTIVE = 1
    private const val SHUTDOWN_REQ = 2
    private const val SHUTDOWN_ACK = 3

    @Volatile
    private var debugStatus: Int = FRESH

    private val isShutdownRequested: Boolean get() {
        val debugStatus = debugStatus
        return debugStatus == SHUTDOWN_REQ || debugStatus == SHUTDOWN_ACK
    }

    override fun run() {
        timeSource.registerTimeLoopThread()
        try {
            var shutdownNanos = Long.MAX_VALUE
            if (!notifyStartup()) return
            while (true) {
                Thread.interrupted() // just reset interruption flag
                var parkNanos = processNextEvent()
                if (parkNanos == Long.MAX_VALUE) {
                    // nothing to do, initialize shutdown timeout
                    if (shutdownNanos == Long.MAX_VALUE) {
                        val now = timeSource.nanoTime()
                        if (shutdownNanos == Long.MAX_VALUE) shutdownNanos = now + KEEP_ALIVE_NANOS
                        val tillShutdown = shutdownNanos - now
                        if (tillShutdown <= 0) return // shut thread down
                        parkNanos = parkNanos.coerceAtMost(tillShutdown)
                    } else
                        parkNanos = parkNanos.coerceAtMost(KEEP_ALIVE_NANOS) // limit wait time anyway
                }
                if (parkNanos > 0) {
                    // check if shutdown was requested and bail out in this case
                    if (isShutdownRequested) return
                    timeSource.parkNanos(this, parkNanos)
                }
            }
        } finally {
            _thread = null // this thread is dead
            acknowledgeShutdownIfNeeded()
            timeSource.unregisterTimeLoopThread()
            // recheck if queues are empty after _thread reference was set to null (!!!)
            if (!isEmpty) thread() // recreate thread if it is needed
        }
    }

    // ensure that thread is there
    private fun thread(): Thread = _thread ?: createThreadSync()

    @Synchronized
    private fun createThreadSync() = _thread ?:
        Thread(this, "kotlinx.coroutines.DefaultExecutor").apply {
            _thread = this
            isDaemon = true
            start()
        }

    override fun unpark() {
        timeSource.unpark(thread()) // as a side effect creates thread if it is not there
    }

    override fun isCorrectThread(): Boolean = true

    // used for tests
    @Synchronized
    internal fun ensureStarted() {
        assert(_thread == null) // ensure we are at a clean state
        assert(debugStatus == FRESH || debugStatus == SHUTDOWN_ACK)
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

    // used for tests
    @Synchronized
    fun shutdown(timeout: Long) {
        val deadline = System.currentTimeMillis() + timeout
        if (!isShutdownRequested) debugStatus = SHUTDOWN_REQ
        // loop while there is anything to do immediately or deadline passes
        while (debugStatus != SHUTDOWN_ACK && _thread != null) {
            _thread?.let { timeSource.unpark(it) } // wake up thread if present
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
}
