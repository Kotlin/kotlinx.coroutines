/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.operators

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import kotlin.test.*

class MapNotNullTest : TestBase() {
    @Test
    fun testMap() = runTest {
        val flow = flow {
            emit(1)
            emit(null)
            emit(2)
        }

        val result = flow.mapNotNull { it }.sum()
        assertEquals(3, result)
    }

    @Test
    fun testEmptyFlow() = runTest {
        val sum = emptyFlow<Int>().mapNotNull { expectUnreached(); it }.sum()
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
                    hang { cancelled = true }
                }
                emit(1)
            }
        }.mapNotNull {
            latch.receive()
            throw TestException()
            it + 1
        }.onErrorReturn(42)

        assertEquals(42, flow.single())
        assertTrue(cancelled)
    }
}
