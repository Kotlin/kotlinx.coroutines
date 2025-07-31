package kotlinx.coroutines.flow

import java.util.concurrent.atomic.AtomicLongArray
import kotlin.random.*
import kotlinx.coroutines.*
import kotlinx.coroutines.testing.*
import org.junit.*

class StateFlowStressTest : TestBase() {
    private val nSeconds = 3 * stressTestMultiplier
    private val state = MutableStateFlow<Long>(0)
    private lateinit var pool: ExecutorCoroutineDispatcher

    @After
    fun tearDown() {
        pool.close()
    }

    fun stress(nEmitters: Int, nCollectors: Int) = runTest {
        pool = newFixedThreadPoolContext(nEmitters + nCollectors, "StateFlowStressTest")
        val collected = Array(nCollectors) { AtomicLongArray(nEmitters) }
        val collectors = launch {
            repeat(nCollectors) { collector ->
                launch(pool) {
                    val c = collected[collector]
                    // collect, but abort and collect again after every 1000 values to stress allocation/deallocation
                    do {
                        val batchSize = Random.nextInt(1..1000)
                        var index = 0
                        val cnt = state.onEach { value ->
                            val emitter = (value % nEmitters).toInt()
                            val current = value / nEmitters
                            // the first value in batch is allowed to repeat, but cannot go back
                            val ok = if (index++ == 0) current >= c[emitter] else current > c[emitter]
                            check(ok) {
                                "Values must be monotonic, but $current is not, " +
                                    "was ${c[emitter]} in collector #$collector from emitter #$emitter"
                            }
                            c[emitter] = current

                        }.take(batchSize).count()
                    } while (cnt == batchSize)
                }
            }
        }
        val emitted = AtomicLongArray(nEmitters)
        val emitters = launch {
            repeat(nEmitters) { emitter ->
                launch(pool) {
                    while (true) {
                        state.value = emitted.incrementAndGet(emitter) * nEmitters + emitter
                        if (emitted[emitter] % 1000 == 0L) yield() // make it cancellable
                    }
                }
            }
        }
        for (second in 1..nSeconds) {
            delay(1000)
            val cs = collected.map { it.sum() }
            println("$second: emitted=${emitted.sum()}, collected=${cs.min()}..${cs.max()}")
        }
        emitters.cancelAndJoin()
        collectors.cancelAndJoin()
        // make sure nothing hanged up
        for (i in 0..<nCollectors) {
            check((0..<nEmitters).any { j -> collected[i][j] > emitted[j] * 0.9 }) {
                "collector #$i failed to collect any of the most recently emitted values"
            }
        }
    }

    private fun AtomicLongArray.sum() = (0..<length()).sumOf(::get)

    @Test
    fun testSingleEmitterAndCollector() = stress(1, 1)

    @Test
    fun testTenEmittersAndCollectors() = stress(10, 10)
}
