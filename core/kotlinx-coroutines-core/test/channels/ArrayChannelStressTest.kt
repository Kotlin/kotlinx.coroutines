/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import org.junit.*
import org.junit.runner.*
import org.junit.runners.*

@RunWith(Parameterized::class)
class ArrayChannelStressTest(private val capacity: Int) : TestBase() {

    companion object {
        @Parameterized.Parameters(name = "{0}, nSenders={1}, nReceivers={2}")
        @JvmStatic
        fun params(): Collection<Array<Any>> = listOf(1, 10, 100, 100_000, 1_000_000).map { arrayOf<Any>(it) }
    }

    @Test
    fun testStress() = runTest {
        val n = 100_000 * stressTestMultiplier
        val q = ArrayChannel<Int>(capacity)
        val sender = launch(kotlin.coroutines.experimental.coroutineContext) {
            for (i in 1..n) {
                q.send(i)
            }
            expect(2)
        }
        val receiver = launch(kotlin.coroutines.experimental.coroutineContext) {
            for (i in 1..n) {
                val next = q.receive()
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
