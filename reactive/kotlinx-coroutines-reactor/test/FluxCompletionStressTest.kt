package kotlinx.coroutines.reactor

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.reactive.*
import org.junit.*
import java.util.*
import kotlin.coroutines.*

class FluxCompletionStressTest : TestBase() {
    private val N_REPEATS = 10_000 * stressTestMultiplier

    private fun CoroutineScope.range(context: CoroutineContext, start: Int, count: Int) = flux(context) {
        for (x in start until start + count) send(x)
    }

    @Test
    fun testCompletion() {
        val rnd = Random()
        repeat(N_REPEATS) {
            val count = rnd.nextInt(5)
            runBlocking {
                withTimeout(5000) {
                    var received = 0
                    range(Dispatchers.Default, 1, count).collect { x ->
                        received++
                        if (x != received) error("$x != $received")
                    }
                    if (received != count) error("$received != $count")
                }
            }
        }
    }
}