package kotlinx.coroutines.channels

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import org.junit.*

class DoubleChannelCloseStressTest : TestBase() {
    private val nTimes = 1000 * stressTestMultiplier

    @Test
    fun testDoubleCloseStress() {
        repeat(nTimes) {
            val actor = GlobalScope.actor<Int>(CoroutineName("actor"), start = CoroutineStart.LAZY) {
                // empty -- just closes channel
            }
            GlobalScope.launch(CoroutineName("sender")) {
                try {
                    actor.send(1)
                } catch (e: ClosedSendChannelException) {
                    // ok -- closed before send
                }
            }
            Thread.sleep(1)
            actor.close()
        }
    }
}
