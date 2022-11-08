/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.scheduling

import kotlinx.coroutines.*
import org.junit.Test
import kotlin.test.*

class SharingWorkerClassTest : SchedulerTestBase() {
    private val threadLocal = ThreadLocal<Int?>()

    @Test
    fun testSharedThread() = runTest {
        val dispatcher = SchedulerCoroutineDispatcher(1, schedulerName = "first")
        val dispatcher2 = SchedulerCoroutineDispatcher(1, schedulerName = "second")

        try {
            withContext(dispatcher) {
                assertNull(threadLocal.get())
                threadLocal.set(239)
                withContext(dispatcher2) {
                    assertNull(threadLocal.get())
                    threadLocal.set(42)
                }

                assertEquals(239, threadLocal.get())
            }
        } finally {
            dispatcher.close()
            dispatcher2.close()
        }
    }

    @Test(timeout = 5000L)
    fun testProgress() = runTest {
        // See #990
        val cores = Runtime.getRuntime().availableProcessors()
        repeat(cores + 1) {
            CoroutineScope(Dispatchers.Default).launch {
                SchedulerCoroutineDispatcher(1).close()
            }.join()
        }
    }
}
