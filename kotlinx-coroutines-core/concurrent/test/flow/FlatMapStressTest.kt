@file:OptIn(ExperimentalAtomicApi::class)

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.internal.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.testing.*
import kotlin.concurrent.atomics.*
import kotlin.test.*

class FlatMapStressTest : TestBase() {

    private val iterations = 2000 * stressTestMultiplier
    private val expectedSum = iterations.toLong() * (iterations + 1) / 2

    @Test
    fun testConcurrencyLevel() = runTest {
        withContext(Dispatchers.Default) {
            testConcurrencyLevel(2)
        }
    }

    @Test
    fun testConcurrencyLevel2() = runTest {
        withContext(Dispatchers.Default) {
            testConcurrencyLevel(3)
        }
    }

    @Test
    fun testBufferSize() = runTest {
        val bufferSize = 5
        withContext(Dispatchers.Default) {
            val inFlightElements = AtomicLong(0L)
            var result = 0L
            (1..iterations step 4).asFlow().flatMapMerge { value ->
                unsafeFlow {
                    repeat(4) {
                        emit(value + it)
                        inFlightElements.incrementAndFetch()
                    }
                }
            }.buffer(bufferSize).collect { value ->
                val inFlight = inFlightElements.load()
                assertTrue(inFlight <= bufferSize + 1,
                    "Expected less in flight elements than ${bufferSize + 1}, but had $inFlight")
                inFlightElements.decrementAndFetch()
                result += value
            }

            assertEquals(0, inFlightElements.load())
            assertEquals(expectedSum, result)
        }
    }

    @Test
    fun testDelivery() = runTest {
        withContext(Dispatchers.Default) {
            val result = (1L..iterations step 4).asFlow().flatMapMerge { value ->
                unsafeFlow {
                    repeat(4) { emit(value + it) }
                }
            }.longSum()
            assertEquals(expectedSum, result)
        }
    }

    @Test
    fun testIndependentShortBursts() = runTest {
        withContext(Dispatchers.Default) {
            repeat(iterations) {
                val result = (1L..4L).asFlow().flatMapMerge { value ->
                    unsafeFlow {
                        emit(value)
                        emit(value)
                    }
                }.longSum()
                assertEquals(20, result)
            }
        }
    }

    private suspend fun testConcurrencyLevel(maxConcurrency: Int) {
        if (maxConcurrency > CONCURRENT_CORE_POOL_SIZE) return
        val concurrency = AtomicLong(0)
        val result = (1L..iterations).asFlow().flatMapMerge(concurrency = maxConcurrency) { value ->
            unsafeFlow {
                val current = concurrency.incrementAndFetch()
                assertTrue(current in 1..maxConcurrency)
                emit(value)
                concurrency.decrementAndFetch()
            }
        }.longSum()

        assertEquals(0, concurrency.load())
        assertEquals(expectedSum, result)
    }
}
