package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import org.junit.*

class DelayChannelTest : TestBase() {

    @Test
    fun testFixedDelayChannelBackpressure() = runBlocking<Unit> {
        val delayChannel = FixedDelayChannel(delay = 100)
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
    fun testDelayChannelBackpressure() = runBlocking<Unit> {
        val delayChannel = DelayChannel(delay = 100)
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
}
