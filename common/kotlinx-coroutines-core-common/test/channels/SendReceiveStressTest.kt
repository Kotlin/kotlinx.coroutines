/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*
import kotlin.test.*

class SendReceiveStressTest : TestBase() {

    // Emulate parametrized by hand :(

    @Test
    fun testArrayChannel() = runTest {
        testStress(ArrayChannel(2))
    }

    @Test
    fun testLinkedListChannel() = runTest {
        testStress(LinkedListChannel())
    }

    @Test
    fun testRendezvousChannel() = runTest {
        testStress(RendezvousChannel())
    }

    private suspend fun testStress(channel: Channel<Int>) = coroutineScope {
        val n = 100 // Do not increase, otherwise node.js will fail with timeout :(
        val sender = launch {
            for (i in 1..n) {
                channel.send(i)
            }
            expect(2)
        }
        val receiver = launch {
            for (i in 1..n) {
                val next = channel.receive()
                check(next == i)
            }
            expect(3)
        }
        expect(1)
        sender.join()
        receiver.join()
        finish(4)
    }
}
