/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class FilterTest : TestBase() {
    @Test
    fun testFilter() = runTest {
        val flow = flowOf(1, 2)
        assertEquals(2, flow.filter { it % 2 == 0 }.sum())
        assertEquals(3, flow.filter { true }.sum())
        assertEquals(0, flow.filter { false }.sum())
    }

    @Test
    fun testEmptyFlow() = runTest {
        val sum = emptyFlow<Int>().filter { true }.sum()
        assertEquals(0, sum)
    }

    @Test
    fun testErrorCancelsUpstream() = runTest {
        var cancelled = false
        val latch = Channel<Unit>()
        val flow = flow {
            coroutineScope {
                launch {
                    latch.send(Unit)
                    hang {cancelled = true}
                }
                emit(1)
            }
        }.filter {
            latch.receive()
            throw TestException()
            true
        }.catch { emit(42) }

        assertEquals(42, flow.single())
        assertTrue(cancelled)
    }


    @Test
    fun testFilterNot() = runTest {
        val flow = flowOf(1, 2)
        assertEquals(0, flow.filterNot { true }.sum())
        assertEquals(3, flow.filterNot { false }.sum())
    }

    @Test
    fun testEmptyFlowFilterNot() = runTest {
        val sum = emptyFlow<Int>().filterNot { true }.sum()
        assertEquals(0, sum)
    }

    @Test
    fun testErrorCancelsUpstreamwFilterNot() = runTest {
        var cancelled = false
        val latch = Channel<Unit>()
        val flow = flow {
            coroutineScope {
                launch {
                    latch.send(Unit)
                    hang {cancelled = true}
                }
                emit(1)
            }
        }.filterNot {
            latch.receive()
            throw TestException()
            true
        }.catch { emit(42) }

        assertEquals(42, flow.single())
        assertTrue(cancelled)
    }
}
