/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class OnEachTest : TestBase() {
    @Test
    fun testOnEach() = runTest {
        val flow = flow {
            emit(1)
            emit(2)
        }

        val result = flow.onEach { expect(it) }.sum()
        assertEquals(3, result)
        finish(3)
    }

    @Test
    fun testEmptyFlow() = runTest {
        val value = emptyFlow<Int>().onEach { fail() }.singleOrNull()
        assertNull(value)
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
        }.onEach {
            latch.receive()
            throw TestException()
            it + 1
        }.onErrorReturn(42)

        assertEquals(42, flow.single())
        assertTrue(cancelled)
    }
}
