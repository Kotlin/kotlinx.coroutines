/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.selects.*
import org.junit.*

class RandevouzChannelStressTest : TestBase() {

    @Test
    fun testStressProducerConsumer() = runTest {
        val n = 100_000 * stressTestMultiplier
        val q = Channel<Int>(Channel.RENDEZVOUS)
        val sender = launch {
            for (i in 1..n) q.send(i)
            expect(2)
        }
        val receiver = launch {
            for (i in 1..n) check(q.receive() == i)
            expect(3)
        }
        expect(1)
        sender.join()
        receiver.join()
        finish(4)
    }

    @Test
    fun testStressProducerConsumerSelects() = runBlocking {
        val n = 100_000 * stressTestMultiplier
        val q = Channel<Int>(Channel.RENDEZVOUS)
        val sender = launch {
            for (i in 1..n) select<Unit> { q.onSend(i) {} }
        }
        val receiver = launch {
            for (i in 1..n) check(select<Int> { q.onReceive { it } } == i)
        }
        sender.join()
        receiver.join()
    }

    @Test
    fun testSelectDeadlockResolution() = runBlocking {
        val n = 100_000 * stressTestMultiplier
        val ch1 = Channel<Int>(Channel.RENDEZVOUS)
        val ch2 = Channel<Int>(Channel.RENDEZVOUS)
        val sender = launch {
            for (i in 1..n) select<Unit> {
                ch1.onSend(i) {}
                ch2.onSend(i) {}
            }
        }
        val receiver = launch {
            for (i in 1..n) select<Unit> {
                ch2.onReceive {}
                ch1.onReceive {}
            }
        }
        sender.join()
        receiver.join()
    }
}
