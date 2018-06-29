/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import org.junit.runner.*
import org.junit.runners.*
import kotlin.coroutines.experimental.*
import kotlin.test.*

@RunWith(Parameterized::class)
class SendReceiveJvmStressTest(private val channel: Channel<Int>) : TestBase() {

    companion object {
        @Parameterized.Parameters(name = "{0}")
        @JvmStatic
        fun params(): Collection<Array<Any>> = listOf(
            ArrayChannel<Int>(1),
            ArrayChannel<Int>(10),
            ArrayChannel<Int>(1_000_000),
            LinkedListChannel<Int>(),
            RendezvousChannel<Int>()
        ).map { arrayOf<Any>(it) }
    }

    @Test
    fun testStress() = runTest {
        val n = 100_000 * stressTestMultiplier
        val sender = launch(coroutineContext) {
            for (i in 1..n) {
                channel.send(i)
            }
            expect(2)
        }
        val receiver = launch(coroutineContext) {
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
