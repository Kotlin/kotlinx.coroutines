/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.reactive.*
import kotlin.test.*

class PublisherAsFlowTest : TestBase() {

    @Test
    fun testCancellation() = runTest {
        var onNext = 0
        var onCancelled = 0
        var onError = 0

        val publisher = publish {
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
        val publisher = publish {
            expect(1)
            send(3)

            expect(2)
            send(5)

            expect(4)
            send(7)
            expect(6)
        }

        publisher.asFlow().collect {
            expect(it)
        }

        finish(8)
    }

    @Test
    fun testBufferSize10() = runTest {
        val publisher = publish {
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
    fun testProduce() = runTest {
        val flow = publish { repeat(10) { send(it) } }.asFlow()
        check(flow.produceIn(this))
        check(flow.buffer(2).produceIn(this))
        check(flow.buffer(Channel.UNLIMITED).produceIn(this))
    }

    private suspend fun check(channel: ReceiveChannel<Int>) {
        val result = ArrayList<Int>(10)
        channel.consumeEach { result.add(it) }
        assertEquals((0..9).toList(), result)
    }
}