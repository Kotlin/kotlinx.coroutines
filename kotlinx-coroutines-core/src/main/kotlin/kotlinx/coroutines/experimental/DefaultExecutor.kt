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

import java.util.concurrent.ScheduledExecutorService
import java.util.concurrent.ScheduledThreadPoolExecutor
import java.util.concurrent.TimeUnit

private const val DEFAULT_KEEP_ALIVE = 1000L

private val KEEP_ALIVE =
    try { java.lang.Long.getLong("kotlinx.coroutines.DefaultExecutor.keepAlive", DEFAULT_KEEP_ALIVE) }
    catch (e: SecurityException) { DEFAULT_KEEP_ALIVE }

@Volatile
private var _executor: ScheduledExecutorService? = null

internal val defaultExecutor: ScheduledExecutorService
    get() = _executor ?: getOrCreateExecutorSync()

@Synchronized
private fun getOrCreateExecutorSync(): ScheduledExecutorService =
    _executor ?: ScheduledThreadPoolExecutor(1) { r ->
        Thread(r, "kotlinx.coroutines.DefaultExecutor").apply { isDaemon = true }
    }.apply {
        setKeepAliveTime(KEEP_ALIVE, TimeUnit.MILLISECONDS)
        allowCoreThreadTimeOut(true)
        executeExistingDelayedTasksAfterShutdownPolicy = false
        // "setRemoveOnCancelPolicy" is available only since JDK7, so try it via reflection
        try {
            val m = this::class.java.getMethod("setRemoveOnCancelPolicy", Boolean::class.javaPrimitiveType)
            m.invoke(this, true)
        } catch (ex: Throwable) { /* ignore */ }
        _executor = this
    }

// used for tests
@Synchronized
internal fun shutdownDefaultExecutor(timeout: Long) {
    _executor?.apply {
        shutdown()
        awaitTermination(timeout, TimeUnit.MILLISECONDS)
        shutdownNow() // ignore all remaining
        _executor = null
    }
}

