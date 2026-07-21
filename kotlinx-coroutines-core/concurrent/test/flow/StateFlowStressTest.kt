@file:OptIn(ExperimentalAtomicApi::class)

package kotlinx.coroutines.flow

import kotlin.concurrent.atomics.*
import kotlinx.coroutines.*
import kotlinx.coroutines.testing.*
import kotlin.random.*
import kotlin.test.*

class StateFlowStressTest : TestBase() {
    private val nSeconds = 3 * stressTestMultiplier
    private val state = MutableStateFlow<Long>(0)

    fun stress(nEmitters: Int, nCollectors: Int) = runTest {
        newFixedThreadPoolContext(nEmitters + nCollectors, "StateFlowStressTest").use { pool ->
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
                                val ok = if (index++ == 0) current >= c.loadAt(emitter) else current > c.loadAt(emitter)
                                check(ok) {
                                    "Values must be monotonic, but $current is not, " +
                                        "was ${c.loadAt(emitter)} in collector #$collector from emitter #$emitter"
                                }
                                c.storeAt(emitter, current)

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
                            state.value = emitted.incrementAndFetchAt(emitter) * nEmitters + emitter
                            if (emitted.loadAt(emitter) % 1000 == 0L) yield() // make it cancellable
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
                check((0..<nEmitters).any { j -> collected[i].loadAt(j) > emitted.loadAt(j) * 0.9 }) {
                    "collector #$i failed to collect any of the most recently emitted values"
                }
            }
        }
    }

    private fun AtomicLongArray.sum() = (0..<size).sumOf(::loadAt)

    @Test
    fun testSingleEmitterAndCollector() = stress(1, 1)

    @Test
    fun testTenEmittersAndCollectors() = stress(10, 10)
}
