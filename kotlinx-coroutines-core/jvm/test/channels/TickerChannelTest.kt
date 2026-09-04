package kotlinx.coroutines.channels

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import org.junit.*
import kotlin.time.Duration.Companion.milliseconds

class TickerChannelTest : TestBase() {
    @Test
    fun testFixedDelayChannelBackpressure() = withVirtualTimeSource {
        runTest {
            val delayChannel = ticker(delayMillis = 1000, initialDelayMillis = 0, mode = TickerMode.FIXED_DELAY)
            delayChannel.receiveSingle()
            delayChannel.checkEmpty()

            delay(1500.milliseconds)
            delayChannel.receiveSingle()
            delay(500.milliseconds)
            delayChannel.checkEmpty()
            delay(520.milliseconds)
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

            delay(1500.milliseconds)
            delayChannel.receiveSingle()
            delay(520.milliseconds)
            delayChannel.receiveSingle()
            delay(500.milliseconds)
            delayChannel.checkEmpty()
            delay(520.milliseconds)
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

            delay(500.milliseconds)
            delayChannel.receiveSingle()
            delay(110.milliseconds)
            delayChannel.receiveSingle()
            delay(110.milliseconds)
            delayChannel.checkEmpty()
            delay(110.milliseconds)
            delayChannel.receiveSingle()
            delayChannel.cancel()
        }
    }
}
