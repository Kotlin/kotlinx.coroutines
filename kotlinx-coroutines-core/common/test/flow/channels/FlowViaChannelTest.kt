/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class FlowViaChannelTest : TestBase() {
    @Test
    fun testRegular() = runTest {
        val flow = flowViaChannel<Int> {
            assertTrue(it.offer(1))
            assertTrue(it.offer(2))
            assertTrue(it.offer(3))
            it.close()
        }
        assertEquals(listOf(1, 2, 3), flow.toList())
    }

    @Test
    fun testBuffer() = runTest {
        val flow = flowViaChannel<Int>(bufferSize = 1) {
            assertTrue(it.offer(1))
            assertTrue(it.offer(2))
            assertFalse(it.offer(3))
            it.close()
        }
        assertEquals(listOf(1, 2), flow.toList())
    }

    @Test
    fun testConflated() = runTest {
        val flow = flowViaChannel<Int>(bufferSize = Channel.CONFLATED) {
            assertTrue(it.offer(1))
            assertTrue(it.offer(2))
            it.close()
        }
        assertEquals(listOf(1), flow.toList())
    }

    @Test
    fun testFailureCancelsChannel() = runTest {
        val flow = flowViaChannel<Int> {
            it.offer(1)
            it.invokeOnClose {
                expect(2)
            }
        }.onEach { throw TestException() }

        expect(1)
        assertFailsWith<TestException>(flow)
        finish(3)
    }

    @Test
    fun testFailureInSourceCancelsConsumer() = runTest {
        val flow = flowViaChannel<Int> {
            expect(2)
            throw TestException()
        }.onEach { expectUnreached() }

        expect(1)
        assertFailsWith<TestException>(flow)
        finish(3)
    }

    @Test
    fun testScopedCancellation() = runTest {
        val flow = flowViaChannel<Int> {
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
