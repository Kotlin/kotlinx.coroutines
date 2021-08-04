/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlin.test.*

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
