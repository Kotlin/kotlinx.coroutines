package kotlinx.coroutines.channels

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import org.junit.*

class TickerChannelTest : TestBase() {
    @Test
    fun testFixedDelayChannelBackpressure() = withVirtualTimeSource {
        runTest {
            val delayChannel = ticker(delayMillis = 1000, initialDelayMillis = 0, mode = TickerMode.FIXED_DELAY)
            delayChannel.receiveSingle()
            delayChannel.checkEmpty()

            delay(1500)
            delayChannel.receiveSingle()
            delay(500)
            delayChannel.checkEmpty()
            delay(520)
            delayChannel.receiveSingle()
            delayChannel.cancel()
        }
    }

    @Test
    fun testDelayChannelBackpressure() = withVirtualTimeSource {
        runTest {
            val delayChannel = ticker(delayMillis = 1000, initialDelayMillis = 0)
            delayChannel.receiveSingle()
            delayChannel.checkEmpty()

            delay(1500)
            delayChannel.receiveSingle()
            delay(520)
            delayChannel.receiveSingle()
            delay(500)
            delayChannel.checkEmpty()
            delay(520)
            delayChannel.receiveSingle()
            delayChannel.cancel()
        }
    }

    @Test
    fun testDelayChannelBackpressure2() = withVirtualTimeSource {
        runTest {
            val delayChannel = ticker(delayMillis = 200, initialDelayMillis = 0)
            delayChannel.receiveSingle()
            delayChannel.checkEmpty()

            delay(500)
            delayChannel.receiveSingle()
            delay(110)
            delayChannel.receiveSingle()
            delay(110)
            delayChannel.checkEmpty()
            delay(110)
            delayChannel.receiveSingle()
            delayChannel.cancel()
        }
    }
}
