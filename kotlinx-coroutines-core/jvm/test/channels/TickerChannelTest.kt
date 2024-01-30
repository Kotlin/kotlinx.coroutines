package kotlinx.coroutines.channels

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import org.junit.*

class TickerChannelTest : TestBase() {
    @Test
    fun testFixedDelayChannelBackpressure() = withVirtualTimeSource {
        runTest {
            val delayChannel = ticker(delayMillis = 1000, initialDelayMillis = 0, mode = TickerMode.FIXED_DELAY)
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
            val delayChannel = ticker(delayMillis = 1000, initialDelayMillis = 0)
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
            val delayChannel = ticker(delayMillis = 200, initialDelayMillis = 0)
            delayChannel.checkNotEmpty()
            delayChannel.checkEmpty()

            delay(500)
            delayChannel.checkNotEmpty()
            delay(110)
            delayChannel.checkNotEmpty()
            delay(110)
            delayChannel.checkEmpty()
            delay(110)
            delayChannel.checkNotEmpty()
            delayChannel.cancel()
        }
    }
}
