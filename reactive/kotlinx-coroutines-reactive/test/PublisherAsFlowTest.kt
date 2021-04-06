/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import org.reactivestreams.*
import kotlin.test.*

class PublisherAsFlowTest : TestBase() {
    @Test
    fun testCancellation() = runTest {
        var onNext = 0
        var onCancelled = 0
        var onError = 0

        val publisher = publish(currentDispatcher()) {
            coroutineContext[Job]?.invokeOnCompletion {
                if (it is CancellationException) ++onCancelled
            }

            repeat(100) {
                send(it)
            }
        }

        publisher.asFlow().launchIn(CoroutineScope(Dispatchers.Unconfined)) {
            onEach {
                ++onNext
                throw RuntimeException()
            }
            catch<Throwable> {
                ++onError
            }
        }.join()


        assertEquals(1, onNext)
        assertEquals(1, onError)
        assertEquals(1, onCancelled)
    }

    @Test
    fun testBufferSize1() = runTest {
        val publisher = publish(currentDispatcher()) {
            expect(1)
            send(3)

            expect(2)
            send(5)

            expect(4)
            send(7)
            expect(6)
        }

        publisher.asFlow().buffer(1).collect {
            expect(it)
        }

        finish(8)
    }

    @Test
    fun testBufferSizeDefault() = runTest {
        val publisher = publish(currentDispatcher()) {
            repeat(64) {
                send(it + 1)
                expect(it + 1)
            }
            assertFalse { offer(-1) }
        }

        publisher.asFlow().collect {
            expect(64 + it)
        }

        finish(129)
    }

    @Test
    fun testDefaultCapacityIsProperlyOverwritten() = runTest {
        val publisher = publish(currentDispatcher()) {
            expect(1)
            send(3)
            expect(2)
            send(5)
            expect(4)
            send(7)
            expect(6)
        }

        publisher.asFlow().flowOn(wrapperDispatcher()).buffer(1).collect {
            expect(it)
        }

        finish(8)
    }

    @Test
    fun testBufferSize10() = runTest {
        val publisher = publish(currentDispatcher()) {
            expect(1)
            send(5)

            expect(2)
            send(6)

            expect(3)
            send(7)
            expect(4)
        }

        publisher.asFlow().buffer(10).collect {
            expect(it)
        }

        finish(8)
    }

    @Test
    fun testConflated() = runTest {
        val publisher = publish(currentDispatcher()) {
            for (i in 1..5) send(i)
        }
        val list = publisher.asFlow().conflate().toList()
        assertEquals(listOf(1, 5), list)
    }

    @Test
    fun testProduce() = runTest {
        val flow = publish(currentDispatcher()) { repeat(10) { send(it) } }.asFlow()
        check((0..9).toList(), flow.produceIn(this))
        check((0..9).toList(), flow.buffer(2).produceIn(this))
        check((0..9).toList(), flow.buffer(Channel.UNLIMITED).produceIn(this))
        check(listOf(0, 9), flow.conflate().produceIn(this))
    }

    private suspend fun check(expected: List<Int>, channel: ReceiveChannel<Int>) {
        val result = ArrayList<Int>(10)
        channel.consumeEach { result.add(it) }
        assertEquals(expected, result)
    }

    @Test
    fun testProduceCancellation() = runTest {
        expect(1)
        // publisher is an async coroutine, so it overproduces to the channel, but still gets cancelled
        val flow = publish(currentDispatcher()) {
            expect(3)
            repeat(10) { value ->
                when (value) {
                    in 0..6 -> send(value)
                    7 -> try {
                        send(value)
                    } catch (e: CancellationException) {
                        expect(5)
                        throw e
                    }
                    else -> expectUnreached()
                }
            }
        }.asFlow().buffer(1)
        assertFailsWith<TestException> {
            coroutineScope {
                expect(2)
                val channel = flow.produceIn(this)
                channel.consumeEach { value ->
                    when (value) {
                        in 0..4 -> {}
                        5 -> {
                            expect(4)
                            throw TestException()
                        }
                        else -> expectUnreached()
                    }
                }
            }
        }
        finish(6)
    }

    @Test
    fun testRequestRendezvous() =
        testRequestSizeWithBuffer(Channel.RENDEZVOUS, BufferOverflow.SUSPEND, 1)

    @Test
    fun testRequestBuffer1() =
        testRequestSizeWithBuffer(1, BufferOverflow.SUSPEND, 1)

    @Test
    fun testRequestBuffer10() =
        testRequestSizeWithBuffer(10, BufferOverflow.SUSPEND, 10)

    @Test
    fun testRequestBufferUnlimited() =
        testRequestSizeWithBuffer(Channel.UNLIMITED, BufferOverflow.SUSPEND, Long.MAX_VALUE)

    @Test
    fun testRequestBufferOverflowSuspend() =
        testRequestSizeWithBuffer(Channel.BUFFERED, BufferOverflow.SUSPEND, 64)

    @Test
    fun testRequestBufferOverflowDropOldest() =
        testRequestSizeWithBuffer(Channel.BUFFERED, BufferOverflow.DROP_OLDEST, Long.MAX_VALUE)

    @Test
    fun testRequestBufferOverflowDropLatest() =
        testRequestSizeWithBuffer(Channel.BUFFERED, BufferOverflow.DROP_LATEST, Long.MAX_VALUE)

    @Test
    fun testRequestBuffer10OverflowDropOldest() =
        testRequestSizeWithBuffer(10, BufferOverflow.DROP_OLDEST, Long.MAX_VALUE)

    @Test
    fun testRequestBuffer10OverflowDropLatest() =
        testRequestSizeWithBuffer(10, BufferOverflow.DROP_LATEST, Long.MAX_VALUE)

    /**
     * Tests `publisher.asFlow.buffer(...)` chain, verifying expected requests size and that only expected
     * values are delivered.
     */
    private fun testRequestSizeWithBuffer(
        capacity: Int,
        onBufferOverflow: BufferOverflow,
        expectedRequestSize: Long
    ) = runTest {
        val m = 50
        // publishers numbers from 1 to m
        val publisher = Publisher<Int> { s ->
            s.onSubscribe(object : Subscription {
                var lastSent = 0
                var remaining = 0L
                override fun request(n: Long) {
                    assertEquals(expectedRequestSize, n)
                    remaining += n
                    check(remaining >= 0)
                    while (lastSent < m && remaining > 0) {
                        s.onNext(++lastSent)
                        remaining--
                    }
                    if (lastSent == m) s.onComplete()
                }

                override fun cancel() {}
            })
        }
        val flow = publisher
            .asFlow()
            .buffer(capacity, onBufferOverflow)
        val list = flow.toList()
        val runSize = if (capacity == Channel.BUFFERED) 1 else capacity
        val expected = when (onBufferOverflow) {
            // Everything is expected to be delivered
            BufferOverflow.SUSPEND -> (1..m).toList()
            // Only the last one (by default) or the last "capacity" items delivered
            BufferOverflow.DROP_OLDEST -> (m - runSize + 1..m).toList()
            // Only the first one (by default) or the first "capacity" items delivered
            BufferOverflow.DROP_LATEST -> (1..runSize).toList()
        }
        assertEquals(expected, list)
    }

    @Test
    fun testException() = runTest {
        expect(1)
        val p = publish<Int> { throw TestException() }.asFlow()
        p.catch {
            assertTrue { it is TestException }
            finish(2)
        }.collect()
    }
}
