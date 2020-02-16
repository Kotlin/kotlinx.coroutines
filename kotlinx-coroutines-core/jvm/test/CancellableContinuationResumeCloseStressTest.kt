/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.atomicfu.*
import org.junit.*
import java.util.concurrent.*
import kotlin.test.*
import kotlin.test.Test

class CancellableContinuationResumeCloseStressTest : TestBase() {
    @get:Rule
    public val dispatcher = ExecutorRule(2)

    private val startBarrier = CyclicBarrier(3)
    private val doneBarrier = CyclicBarrier(2)
    private val nRepeats = 1_000 * stressTestMultiplier

    private val closed = atomic(false)
    private var returnedOk = false

    @Test
    @Suppress("BlockingMethodInNonBlockingContext")
    fun testStress() = runTest {
        repeat(nRepeats) {
            closed.value = false
            returnedOk = false
            val job = testJob()
            startBarrier.await()
            job.cancel() // (1) cancel job
            job.join()
            // check consistency
            doneBarrier.await()
            if (returnedOk) {
                assertFalse(closed.value, "should not have closed resource -- returned Ok")
            } else {
                assertTrue(closed.value, "should have closed resource -- was cancelled")
            }
        }
    }

    private fun CoroutineScope.testJob(): Job = launch(dispatcher, start = CoroutineStart.ATOMIC) {
        val ok = resumeClose() // might be cancelled
        assertEquals("OK", ok)
        returnedOk = true
    }

    private suspend fun resumeClose() = suspendCancellableCoroutine<String> { cont ->
        dispatcher.executor.execute {
            startBarrier.await() // (2) resume at the same time
            cont.resume("OK") {
                close()
            }
            doneBarrier.await()
        }
        startBarrier.await() // (3) return at the same time
    }

    fun close() {
        assertFalse(closed.getAndSet(true))
    }
}
