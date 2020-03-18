/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.jdk9

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import kotlin.test.*

class PublisherAsFlowTest : TestBase() {
    @Test
    fun testCancellation() = runTest {
        var onNext = 0
        var onCancelled = 0
        var onError = 0

        val publisher = flowPublish(currentDispatcher()) {
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
        val publisher = flowPublish(currentDispatcher()) {
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
        val publisher = flowPublish(currentDispatcher()) {
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
        val publisher = flowPublish(currentDispatcher()) {
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
        val publisher = flowPublish(currentDispatcher()) {
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
        val publisher = flowPublish(currentDispatcher()) {
            for (i in 1..5) send(i)
        }
        val list = publisher.asFlow().conflate().toList()
        assertEquals(listOf(1, 5), list)
    }

    @Test
    fun testProduce() = runTest {
        val flow = flowPublish(currentDispatcher()) { repeat(10) { send(it) } }.asFlow()
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
        val flow = flowPublish(currentDispatcher()) {
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
}
