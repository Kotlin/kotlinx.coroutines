package flow

import kotlinx.coroutines.TestBase
import kotlinx.coroutines.cancelAndJoin
import kotlinx.coroutines.delay
import kotlinx.coroutines.flow.launchIn
import kotlinx.coroutines.flow.onEach
import kotlinx.coroutines.flow.tickerFlow
import java.util.concurrent.CancellationException
import kotlin.test.Test
import kotlin.test.assertEquals


class TickerFlowTest : TestBase() {

    @Test(expected = IllegalArgumentException::class)
    fun testNegativePeriod() = runTest {
        // WHEN
        tickerFlow(-1).launchIn(this)
    }

    @Test(expected = IllegalArgumentException::class)
    fun testZeroNegativePeriod() = runTest {
        // WHEN
        tickerFlow(0).launchIn(this)
    }

    @Test(expected = IllegalArgumentException::class)
    fun testNegativeInitialDelay() = runTest {
        // WHEN
        tickerFlow(100, -1).launchIn(this)
    }

    @Test
    fun testInitialDelay() = runTest {
        // GIVEN
        val inbox = mutableListOf<Unit>()

        // WHEN
        val periodicTicker =
                tickerFlow(100, 100).onEach {
                    inbox.add(Unit)
                }.launchIn(this)

        delay(500)

        // THEN
        assertEquals(4, inbox.size)

        periodicTicker.cancelAndJoin()
    }


    @Test
    fun testReceive() = runTest {
        // GIVEN
        val inbox = mutableListOf<Unit>()

        // WHEN
        val periodicTicker =
                tickerFlow(100).onEach {
                    inbox.add(Unit)
                }.launchIn(this)

        delay(500)

        // THEN
        assertEquals(4, inbox.size)

        periodicTicker.cancelAndJoin()
    }

    @Test
    fun testDoNotReceiveAfterCancel() = runTest {
        // GIVEN
        val inbox = mutableListOf<Unit>()

        // WHEN
        val periodicTicker =
                tickerFlow(100).onEach {
                    inbox.add(Unit)
                }.launchIn(this)

        delay(50)

        // THEN
        assertEquals(0, inbox.size)
        periodicTicker.cancel(CancellationException())
    }


}