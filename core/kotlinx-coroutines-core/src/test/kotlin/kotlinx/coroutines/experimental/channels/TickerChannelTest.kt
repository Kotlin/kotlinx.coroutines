package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import org.junit.*

class TickerChannelTest : TestBase() {

    @Test
    fun testFixedDelayChannelBackpressure() = runTest {
        val delayChannel = fixedTicker(delay = 100, initialDelay = 0)
        delayChannel.checkNotEmpty()
        delayChannel.checkEmpty()

        delay(150)
        delayChannel.checkNotEmpty()
        delay(50)
        delayChannel.checkEmpty()
        delay(52)
        delayChannel.checkNotEmpty()
        delayChannel.cancel()
    }

    @Test
    fun testDelayChannelBackpressure() = runTest {
        val delayChannel = ticker(delay = 100, initialDelay = 0)
        delayChannel.checkNotEmpty()
        delayChannel.checkEmpty()

        delay(150)
        delayChannel.checkNotEmpty()
        delay(52)
        delayChannel.checkNotEmpty()
        delay(50)
        delayChannel.checkEmpty()
        delay(52)
        delayChannel.checkNotEmpty()
        delayChannel.cancel()
    }

    @Test
    fun testDelayChannelBackpressure2() = runTest {
        val delayChannel = ticker(delay = 100, initialDelay = 0)
        delayChannel.checkNotEmpty()
        delayChannel.checkEmpty()

        delay(250)
        delayChannel.checkNotEmpty()
        delay(51)
        delayChannel.checkNotEmpty()
        delay(51)
        delayChannel.checkEmpty()
        delay(51)
        delayChannel.checkNotEmpty()
        delayChannel.cancel()
    }
}
