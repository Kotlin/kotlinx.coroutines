/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.scheduling.*
import org.junit.Assume.*
import org.junit.Test
import java.util.concurrent.atomic.*
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
            (1..iterations step 4).asFlow().flatMapMerge(bufferSize = bufferSize) { value ->
                unsafeFlow {
                    repeat(4) {
                        emit(value + it)
                        inFlightElements.incrementAndGet()
                    }
                }
            }.collect { value ->
                val inFlight = inFlightElements.get()
                assertTrue(inFlight <= bufferSize + 1,
                    "Expected less in flight elements than ${bufferSize + 1}, but had $inFlight")
                inFlightElements.decrementAndGet()
                result += value
            }

            assertEquals(0, inFlightElements.get())
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
        assumeTrue(maxConcurrency <= CORE_POOL_SIZE)
        val concurrency = AtomicLong()
        val result = (1L..iterations).asFlow().flatMapMerge(concurrency = maxConcurrency) { value ->
            unsafeFlow {
                val current = concurrency.incrementAndGet()
                assertTrue(current in 1..maxConcurrency)
                emit(value)
                concurrency.decrementAndGet()
            }
        }.longSum()

        assertEquals(0, concurrency.get())
        assertEquals(expectedSum, result)
    }
}
