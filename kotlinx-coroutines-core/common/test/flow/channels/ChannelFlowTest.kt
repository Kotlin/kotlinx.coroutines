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
        val flow = channelFlow {
            assertTrue(offer(1))
            assertTrue(offer(2))
            assertFalse(offer(3))
        }.buffer(1)
        assertEquals(listOf(1, 2), flow.toList())
    }

    @Test
    fun testConflated() = runTest {
        val flow = channelFlow {
            assertTrue(offer(1))
            assertTrue(offer(2))
            assertTrue(offer(3))
            assertTrue(offer(4))
        }.buffer(Channel.CONFLATED)
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

    @Test
    fun testMergeOneCoroutineWithCancellation() = runTest {
        val flow = flowOf(1, 2, 3)
        val f = flow.mergeOneCoroutine(flow).take(2)
        assertEquals(listOf(1, 1), f.toList())
    }

    @Test
    fun testMergeTwoCoroutinesWithCancellation() = runTest {
        val flow = flowOf(1, 2, 3)
        val f = flow.mergeTwoCoroutines(flow).take(2)
        assertEquals(listOf(1, 1), f.toList())
    }

    private fun Flow<Int>.mergeTwoCoroutines(other: Flow<Int>): Flow<Int> = channelFlow {
        launch {
            collect { send(it); yield() }
        }
        launch {
            other.collect { send(it) }
        }
    }

    private fun Flow<Int>.mergeOneCoroutine(other: Flow<Int>): Flow<Int> = channelFlow {
        launch {
            collect { send(it); yield() }
        }

        other.collect { send(it); yield() }
    }

    @Test
    @Ignore // #1374
    fun testBufferWithTimeout() = runTest {
        fun Flow<Int>.bufferWithTimeout(): Flow<Int> = channelFlow {
            expect(2)
            launch {
                expect(3)
                hang {
                    expect(5)
                }
            }
            launch {
                expect(4)
                collect {
                    withTimeout(-1) {
                        send(it)
                    }
                    expectUnreached()
                }
                expectUnreached()
            }
        }

        val flow = flowOf(1, 2, 3).bufferWithTimeout()
        expect(1)
        assertFailsWith<TimeoutCancellationException>(flow)
        finish(6)
    }

    @Test
    fun testChildCancellation() = runTest {
        channelFlow {
            val job = launch {
                expect(2)
                hang { expect(4) }
            }
            expect(1)
            yield()
            expect(3)
            job.cancelAndJoin()
            send(5)

        }.collect {
            expect(it)
        }

        finish(6)
    }
}
