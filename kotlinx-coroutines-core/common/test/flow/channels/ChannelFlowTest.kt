/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class ChannelFlowTest : TestBase() {
    @Test
    fun testRegular() = runTest {
        val flow = channelFlow {
            assertTrue(trySend(1).isSuccess)
            assertTrue(trySend(2).isSuccess)
            assertTrue(trySend(3).isSuccess)
        }
        assertEquals(listOf(1, 2, 3), flow.toList())
    }

    @Test
    fun testBuffer() = runTest {
        val flow = channelFlow {
            assertTrue(trySend(1).isSuccess)
            assertTrue(trySend(2).isSuccess)
            assertFalse(trySend(3).isSuccess)
        }.buffer(1)
        assertEquals(listOf(1, 2), flow.toList())
    }

    @Test
    fun testConflated() = runTest {
        val flow = channelFlow {
            assertTrue(trySend(1).isSuccess)
            assertTrue(trySend(2).isSuccess)
            assertTrue(trySend(3).isSuccess)
            assertTrue(trySend(4).isSuccess)
        }.buffer(Channel.CONFLATED)
        assertEquals(listOf(1, 4), flow.toList()) // two elements in the middle got conflated
    }

    @Test
    fun testFailureCancelsChannel() = runTest {
        val flow = channelFlow {
            trySend(1)
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

    @Test
    fun testClosedPrematurely() = runTest(unhandled = listOf({ e -> e is ClosedSendChannelException })) {
        val outerScope = this
        val flow = channelFlow {
            // ~ callback-based API, no children
            outerScope.launch(Job()) {
                expect(2)
                send(1)
                expectUnreached()
            }
            expect(1)
        }
        assertEquals(emptyList(), flow.toList())
        finish(3)
    }

    @Test
    fun testNotClosedPrematurely() = runTest {
        val outerScope = this
        val flow = channelFlow {
            // ~ callback-based API
            outerScope.launch(Job()) {
                expect(2)
                send(1)
                close()
            }
            expect(1)
            awaitClose()
        }

        assertEquals(listOf(1), flow.toList())
        finish(3)
    }

    @Test
    fun testCancelledOnCompletion() = runTest {
        val myFlow = callbackFlow<Any> {
            expect(2)
            close()
            hang { expect(3) }
        }

        expect(1)
        myFlow.collect()
        finish(4)
    }
}
