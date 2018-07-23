/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import org.junit.*

class TickerChannelTest : TestBase() {
    @Test
    fun testFixedDelayChannelBackpressure() = withVirtualTimeSource {
        runTest {
            val delayChannel = ticker(delay = 1000, initialDelay = 0, mode = TickerMode.FIXED_DELAY)
            delayChannel.checkNotEmpty()
            delayChannel.checkEmpty()

            delay(1500)
            delayChannel.checkNotEmpty()
            delay(500)
            delayChannel.checkEmpty()
            delay(520)
            delayChannel.checkNotEmpty()
            delayChannel.cancel()
        }
    }

    @Test
    fun testDelayChannelBackpressure() = withVirtualTimeSource {
        runTest {
            val delayChannel = ticker(delay = 1000, initialDelay = 0)
            delayChannel.checkNotEmpty()
            delayChannel.checkEmpty()

            delay(1500)
            delayChannel.checkNotEmpty()
            delay(520)
            delayChannel.checkNotEmpty()
            delay(500)
            delayChannel.checkEmpty()
            delay(520)
            delayChannel.checkNotEmpty()
            delayChannel.cancel()
        }
    }

    @Test
    fun testDelayChannelBackpressure2() = withVirtualTimeSource {
        runTest {
            val delayChannel = ticker(delay = 1000, initialDelay = 0)
            delayChannel.checkNotEmpty()
            delayChannel.checkEmpty()

            delay(2500)
            delayChannel.checkNotEmpty()
            delay(510)
            delayChannel.checkNotEmpty()
            delay(510)
            delayChannel.checkEmpty()
            delay(510)
            delayChannel.checkNotEmpty()
            delayChannel.cancel()
        }
    }
}
