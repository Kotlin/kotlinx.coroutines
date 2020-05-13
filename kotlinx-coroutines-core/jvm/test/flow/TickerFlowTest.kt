package flow

import kotlinx.coroutines.TestBase
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
    fun testZeroPeriod() = runTest {
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
        tickerFlow(100, 200).onEach {
            inbox.add(Unit)
        }.launchIn(this)

        delay(500)

        // THEN
        assertEquals(4, inbox.size)
    }

    @Test
    fun testZeroInitialDelay() = runTest {
        // GIVEN
        val inbox = mutableListOf<Unit>()

        // WHEN
        tickerFlow(100, 0).onEach {
            inbox.add(Unit)
        }.launchIn(this)

        delay(500)

        // THEN
        assertEquals(6, inbox.size)
    }


    @Test
    fun testReceive() = runTest {
        // GIVEN
        val inbox = mutableListOf<Unit>()

        // WHEN
        tickerFlow(100).onEach {
            inbox.add(Unit)
        }.launchIn(this)

        delay(500)

        // THEN
        assertEquals(5, inbox.size)
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
        periodicTicker.cancel(CancellationException())

        // THEN
        assertEquals(0, inbox.size)
    }
}