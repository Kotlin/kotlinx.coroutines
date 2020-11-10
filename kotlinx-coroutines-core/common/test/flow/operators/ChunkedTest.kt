/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*
import kotlin.time.*

@ExperimentalTime
class ChunkedTest : TestBase() {

    private val testFlow = flow<Int> {
        delay(10)
        for (i in 1..10_000_000) {
            emit(i)
//            delay(500)
//            for (j in 1..100_000) {
//                emit(j)
//            }
        }
    }

    private fun <T> Flow<T>.channelTransform() = channelFlow {
        val inbox = produceIn(this)
        repeat(4) {
            launch(Dispatchers.Default) {
                for (value in inbox) send(value.toString().toInt() * 2)
            }
        }
    }

    @Test
    fun testLazy() = runTest {
        launch(Dispatchers.Default) {
            var emissionsCount = 0
            testFlow.chunkedNonResetableTimer(100, false)
                .onEach { emissionsCount += it.size }
                .count()
                .let { println("chunks: $it, total emissions: $emissionsCount") }
        }
    }

    @Test
    fun testEager() = runTest {
        launch(Dispatchers.Default) {
            var emissionsCount = 0
            testFlow.chunkedNonResetableTimer(100, true)
                .onEach { emissionsCount += it.size }
                .count()
                .let { println("chunks: $it, total emissions: $emissionsCount") }
        }
    }

    @Test
    fun testSelectFixedInterval() = runTest {
        launch(Dispatchers.Default) {
            var emissionsCount = 0
            testFlow.chunked(100.toDuration(DurationUnit.MILLISECONDS), minSize = 0)
                .onEach { emissionsCount += it.size }
                .count()
                .let { println("chunks: $it, total emissions: $emissionsCount") }
        }
    }

    @Test
    fun testSelectFloatingInterval() = runTest {
        launch(Dispatchers.Default) {
            var emissionsCount = 0
            testFlow.chunked(100.toDuration(DurationUnit.MILLISECONDS))
                .onEach { emissionsCount += it.size }
                .count()
                .let { println("chunks: $it, total emissions: $emissionsCount") }
        }
    }

    @Test
    fun testChunkNoMaxTime() = runTest {
        launch(Dispatchers.Default) {
            var emissionsCount = 0
            testFlow.chunkFixedTimeWindows(100)
                .onEach { emissionsCount += it.size }
                .count()
                .let { println("chunks: $it, total emissions: $emissionsCount") }
        }
    }

    @Test
    fun testEmptyFlow() = runTest {
        val emptyFlow = emptyFlow<Int>()
        val result = emptyFlow.chunked(1000).toList()

        assertTrue { result.isEmpty() }
    }

    @ExperimentalTime
    @Test
    fun testSingleFastElement() = runTest {
        val fastFlow = flow { emit(1) }
        val result = measureTimedValue {
            fastFlow.chunked(10_000).toList()
        }

        assertTrue { result.value.size == 1 && result.value.first().contains(1) }
        assertTrue { result.duration.inSeconds < 1 }
    }

    @Test
    fun testWindowsChunkingWithNoMinimumSize() = withVirtualTime {
        val intervalFlow = flow {
            delay(1500)
            emit(1)
            delay(1500)
            emit(2)
            delay(1500)
            emit(3)
        }
        val chunks = intervalFlow.chunked(2.toDuration(DurationUnit.SECONDS), minSize = 0).toList()

        assertEquals (3, chunks.size)
        assertTrue { chunks.all { it.size == 1 } }

        finish(1)
    }

    @Test
    fun testNonContinousWindowsChunking() = withVirtualTime {
        val intervalFlow = flow {
            delay(1500)
            emit(1)
            delay(1500)
            emit(2)
            delay(1500)
            emit(3)
        }
        val chunks = intervalFlow.chunked(2.toDuration(DurationUnit.SECONDS)).toList()

        assertEquals (2, chunks.size)
        assertTrue { chunks.first().size == 2 && chunks[1].size == 1 }

        finish(1)
    }

    @Test
    fun testRespectingMinValue() = withVirtualTime {
        val intervalFlow = flow {
            delay(1500)
            emit(1)
            delay(1500)
            emit(2)
            delay(1500)
            emit(3)
        }
        val chunks = intervalFlow.chunked(2000, minSize = 3).toList()

        assertTrue { chunks.size == 1 }
        assertTrue { chunks.first().size == 3 }

        finish(1)
    }

    @Test
    fun testRespectingMaxValueWithContinousWindows() = withVirtualTime {
        val intervalFlow = flow {
            delay(1500)
            emit(1)
            emit(2)
            emit(3)
            emit(4)
            delay(1500)
            emit(5)
            delay(1500)
            emit(6)
        }
        val chunks = intervalFlow.chunked(2000, minSize = 0, maxSize = 3).toList()

        assertEquals(3, chunks.size)
        assertEquals(3, chunks.first().size)
        assertEquals(2, chunks[1].size)
        assertTrue { chunks[1].containsAll(listOf(4, 5)) }

        finish(1)
    }

    @Test
    fun testRespectingMaxValueAndResetingTickerWithNonContinousWindows() = withVirtualTime {
        val intervalFlow = flow {
            delay(1500)
            emit(1)
            emit(2)
            emit(3)
            delay(1500)
            emit(4)
            emit(5)
            delay(1500)
            emit(6)
        }
        val chunks = intervalFlow.chunked(2000, maxSize = 3).toList()

        assertEquals(2, chunks.size)
        assertEquals(3, chunks.first().size)
        assertEquals(3, chunks[1].size)
        assertTrue { chunks[1].containsAll(listOf(4, 5, 6)) }

        finish(1)
    }

    @Test
    fun testSizeBasedChunking() = runTest {
        val flow = flow {
            for (i in 1..10) emit(i)
        }

        val chunks = flow.chunked(maxSize = 3).toList()

        assertEquals(4, chunks.size)
    }

    @Test
    fun testSizeBasedChunkingWithMinSize() = runTest {
        val flow = flow {
            for (i in 1..10) emit(i)
        }

        val chunks = flow.chunked(maxSize = 3, minSize = 2).toList()

        assertEquals(3, chunks.size)
    }

}