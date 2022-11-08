/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import org.junit.Test
import java.lang.Runnable
import java.util.concurrent.*
import kotlin.test.*

class ExecutorAsCoroutineDispatcherDelayTest : TestBase() {

    private var callsToSchedule = 0

    private inner class STPE : ScheduledThreadPoolExecutor(1) {
        override fun schedule(command: Runnable, delay: Long, unit: TimeUnit): ScheduledFuture<*> {
            if (delay != 0L) ++callsToSchedule
            return super.schedule(command, delay, unit)
        }
    }

    private inner class SES : ScheduledExecutorService by STPE()

    @Test
    fun testScheduledThreadPool() = runTest {
        val executor = STPE()
        withContext(executor.asCoroutineDispatcher()) {
            delay(100)
        }
        executor.shutdown()
        assertEquals(1, callsToSchedule)
    }

    @Test
    fun testScheduledExecutorService() = runTest {
        val executor = SES()
        withContext(executor.asCoroutineDispatcher()) {
            delay(100)
        }
        executor.shutdown()
        assertEquals(1, callsToSchedule)
    }
}
