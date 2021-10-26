/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlin.test.*

class TestRunBlockingOrderTest {

    private val actionIndex = atomic(0)
    private val finished = atomic(false)

    private fun expect(index: Int) {
        val wasIndex = actionIndex.incrementAndGet()
        check(index == wasIndex) { "Expecting action index $index but it is actually $wasIndex" }
    }

    private fun finish(index: Int) {
        expect(index)
        check(!finished.getAndSet(true)) { "Should call 'finish(...)' at most once" }
    }

    @Test
    fun testLaunchImmediate() = runBlockingTest {
        expect(1)
        launch {
            expect(2)
        }
        finish(3)
    }

    @Test
    fun testYield() = runBlockingTest {
        expect(1)
        launch {
            expect(2)
            yield()
            finish(4)
        }
        expect(3)
    }

    @Test
    fun testLaunchWithDelayCompletes() = runBlockingTest {
        expect(1)
        launch {
            delay(100)
            finish(3)
        }
        expect(2)
    }

    @Test
    fun testLaunchDelayOrdered() = runBlockingTest {
        expect(1)
        launch {
            delay(200) // long delay
            finish(4)
        }
        launch  {
            delay(100) // shorter delay
            expect(3)
        }
        expect(2)
    }

    @Test
    fun testVeryLongDelay() = runBlockingTest {
        expect(1)
        delay(100) // move time forward a bit some that naive time + delay gives an overflow
        launch {
            delay(Long.MAX_VALUE / 2) // very long delay
            finish(4)
        }
        launch  {
            delay(100) // short delay
            expect(3)
        }
        expect(2)
    }

    @Test
    fun testAdvanceUntilIdle_inRunBlocking() = runBlockingTest {
        expect(1)
        assertRunsFast {
            advanceUntilIdle()   // ensure this doesn't block forever
        }
        finish(2)
    }
}
