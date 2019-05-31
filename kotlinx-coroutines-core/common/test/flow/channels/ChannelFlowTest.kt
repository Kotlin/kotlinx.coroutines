/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class ChannelFlowTest : TestBase() {
    @Test
    fun testRegular() = runTest {
        val flow = channelFlow {
            assertTrue(offer(1))
            assertTrue(offer(2))
            assertTrue(offer(3))
        }
        assertEquals(listOf(1, 2, 3), flow.toList())
    }

    @Test
    fun testBuffer() = runTest {
        val flow = channelFlow(bufferSize = 1) {
            assertTrue(offer(1))
            assertTrue(offer(2))
            assertFalse(offer(3))
        }
        assertEquals(listOf(1, 2), flow.toList())
    }

    @Test
    fun testConflated() = runTest {
        val flow = channelFlow(bufferSize = Channel.CONFLATED) {
            assertTrue(offer(1))
            assertTrue(offer(2))
            assertTrue(offer(3))
            assertTrue(offer(4))
        }
        assertEquals(listOf(1, 4), flow.toList()) // two elements in the middle got conflated
    }

    @Test
    fun testFailureCancelsChannel() = runTest {
        val flow = channelFlow {
            offer(1)
            invokeOnClose {
                expect(2)
            }
        }.onEach { throw TestException() }

        expect(1)
        assertFailsWith<TestException>(flow)
        finish(3)
    }

    @Test
    fun testFailureInSourceCancelsConsumer() = runTest {
        val flow = channelFlow<Int> {
            expect(2)
            throw TestException()
        }.onEach { expectUnreached() }

        expect(1)
        assertFailsWith<TestException>(flow)
        finish(3)
    }

    @Test
    fun testScopedCancellation() = runTest {
        val flow = channelFlow<Int> {
            expect(2)
            launch(start = CoroutineStart.ATOMIC) {
                hang { expect(3) }
            }
            throw TestException()
        }.onEach { expectUnreached() }

        expect(1)
        assertFailsWith<TestException>(flow)
        finish(4)
    }
}
