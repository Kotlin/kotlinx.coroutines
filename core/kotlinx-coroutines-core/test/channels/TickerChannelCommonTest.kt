/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.selects.*
import org.junit.Test
import org.junit.runner.*
import org.junit.runners.*
import kotlin.test.*

@RunWith(Parameterized::class)
class TickerChannelCommonTest(private val channelFactory: Channel) : TestBase() {
    companion object {
        @Parameterized.Parameters(name = "{0}")
        @JvmStatic
        fun params(): Collection<Array<Any>> =
            Channel.values().map { arrayOf<Any>(it) }
    }

    enum class Channel {
        FIXED_PERIOD {
            override fun invoke(delay: Long, initialDelay: Long) =
                ticker(delay, initialDelay = initialDelay, mode = TickerMode.FIXED_PERIOD)
        },

        FIXED_DELAY {
            override fun invoke(delay: Long, initialDelay: Long) =
                ticker(delay, initialDelay = initialDelay, mode = TickerMode.FIXED_DELAY)
        };

        abstract operator fun invoke(delay: Long, initialDelay: Long = 0): ReceiveChannel<Unit>
    }

    @Test
    fun testDelay() = runTest {
        val delayChannel = channelFactory(delay = 100)
        delayChannel.checkNotEmpty()
        delayChannel.checkEmpty()

        delay(50)
        delayChannel.checkEmpty()
        delay(51)
        delayChannel.checkNotEmpty()

        delayChannel.cancel()
        delay(51)
        delayChannel.checkEmpty()
        delayChannel.cancel()
    }

    @Test
    fun testInitialDelay() = runTest {
        val delayChannel = channelFactory(initialDelay = 75, delay = 100)
        delayChannel.checkEmpty()
        delay(50)
        delayChannel.checkEmpty()
        delay(30)
        delayChannel.checkNotEmpty()

        // Regular delay
        delay(75)
        delayChannel.checkEmpty()
        delay(26)
        delayChannel.checkNotEmpty()
        delayChannel.cancel()
    }


    @Test
    fun testReceive() = runTest {
        val delayChannel = channelFactory(delay = 100)
        delayChannel.checkNotEmpty()
        var value = withTimeoutOrNull(75) {
            delayChannel.receive()
            1
        }

        assertNull(value)
        value = withTimeoutOrNull(26) {
            delayChannel.receive()
            1
        }

        assertNotNull(value)
        delayChannel.cancel()
    }

    @Test
    fun testComplexOperator() = runTest {
        val producer = produce {
            for (i in 1..7) {
                send(i)
                delay(100)
            }
        }

        val averages = producer.averageInTimeWindow(300).toList()
        assertEquals(listOf(2.0, 5.0, 7.0), averages)
    }

    private fun ReceiveChannel<Int>.averageInTimeWindow(timespan: Long) = produce {
        val delayChannel = channelFactory(delay = timespan, initialDelay = timespan)
        var sum = 0
        var n = 0
        whileSelect {
            this@averageInTimeWindow.onReceiveOrNull {
                when (it) {
                    null -> {
                        // Send leftovers and bail out
                        if (n != 0) send(sum / n.toDouble())
                        false
                    }
                    else -> {
                        sum += it
                        ++n
                        true
                    }
                }
            }

            // Timeout, send aggregated average and reset counters
            delayChannel.onReceive {
                send(sum / n.toDouble())
                sum = 0
                n = 0
                true
            }
        }

        delayChannel.cancel()
    }

    @Test
    fun testStress() = runTest {
        // No OOM/SOE
        val iterations = 100_000 * stressTestMultiplier
        val delayChannel = channelFactory(0)
        repeat(iterations) {
            delayChannel.receive()
        }

        delayChannel.cancel()
    }

    @Test(expected = IllegalArgumentException::class)
    fun testNegativeDelay() {
        channelFactory(-1)
    }

    @Test(expected = IllegalArgumentException::class)
    fun testNegativeInitialDelay() {
        channelFactory(initialDelay = -1, delay = 100)
    }
}

fun ReceiveChannel<Unit>.checkEmpty() = assertNull(poll())

fun ReceiveChannel<Unit>.checkNotEmpty() {
    assertNotNull(poll())
    assertNull(poll())
}
