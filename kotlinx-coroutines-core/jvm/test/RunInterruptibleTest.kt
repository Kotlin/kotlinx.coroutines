/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.channels.*
import java.io.*
import java.util.concurrent.*
import java.util.concurrent.atomic.*
import kotlin.test.*

class RunInterruptibleTest : TestBase() {

    @Test
    fun testNormalRun() = runTest {
        val result = runInterruptible {
            val x = 1
            val y = 2
            Thread.sleep(1)
            x + y
        }
        assertEquals(3, result)
    }

    @Test
    fun testExceptionalRun() = runTest {
        try {
            runInterruptible {
                expect(1)
                throw TestException()
            }
        } catch (e: TestException) {
            finish(2)
        }
    }

    @Test
    fun testInterrupt() = runTest {
        val latch = Channel<Unit>(1)
        val job = launch {
            runInterruptible(Dispatchers.IO) {
                expect(2)
                latch.offer(Unit)
                try {
                    Thread.sleep(10_000L)
                    expectUnreached()
                } catch (e: InterruptedException) {
                    expect(4)
                    assertFalse { Thread.currentThread().isInterrupted }
                }
            }
        }

        launch(start = CoroutineStart.UNDISPATCHED) {
            expect(1)
            latch.receive()
            expect(3)
            job.cancelAndJoin()
        }.join()
        finish(5)
    }
}
