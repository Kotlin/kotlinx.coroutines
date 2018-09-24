/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import org.junit.*

class RandevouzChannelStressTest : TestBase() {

    @Test
    fun testStress() = runTest {
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
}
