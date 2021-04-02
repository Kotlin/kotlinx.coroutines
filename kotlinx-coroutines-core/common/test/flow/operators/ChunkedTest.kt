/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*
import kotlin.time.*

@ExperimentalTime
class ChunkedTest : TestBase() {

    @Test
    fun testEmptyFlowSizeBasedChunking() = runTest {
        val emptyFlow = emptyFlow<Int>()
        val result = emptyFlow.chunked(ChunkingMethod.BySize(5)).toList()
        assertTrue(result.isEmpty())
    }

    @Test
    fun testUndersizedFlowSizeBasedChunking() = runTest {
        val undersizeFlow = flow<Int> {
            for (i in 1..3) emit(i)
        }
        val result = undersizeFlow.chunked(ChunkingMethod.BySize(5)).toList()
        assertEquals(1, result.size)
        assertEquals(listOf(1, 2, 3), result.first())
    }

    @Test
    fun testOversizedFlowSizeBasedChunking() = runTest {
        val oversizedFlow = flow<Int> {
            for (i in 1..10) emit(i)
        }
        val result = oversizedFlow.chunked(ChunkingMethod.BySize(3)).toList()
        assertEquals(4, result.size)
        assertEquals(3, result.first().size)
        assertEquals(1, result[3].size)

    }

    @Test
    fun testEmptyFlowNaturalChunking() = runTest {
        val emptyFlow = emptyFlow<Int>()
        val result = emptyFlow.chunked(ChunkingMethod.Natural()).toList()
        assertTrue(result.isEmpty())
    }

    @Test
    fun testFastCollectorNaturalChunking() = withVirtualTime {
        val slowProducer = flow<Int> {
            for (i in 1..10) {
                delay(5)
                emit(i)
            }
        }

        val result = slowProducer.chunked(ChunkingMethod.Natural()).toList()
        assertEquals(10, result.size)
        result.forEach { assertEquals(1, it.size) }

        finish(1)
    }

    @Test
    fun testSlowCollectorNaturalChunking() = withVirtualTime {
        val producerInterval = 5L
        val fastProducer = flow<Int> {
            emit(1)
            expect(1)
            delay(producerInterval)

            emit(2)
            expect(3)
            delay(producerInterval)

            emit(3)
            expect(4)
            delay(producerInterval)

            emit(4)
            expect(6)
            delay(producerInterval)

            emit(5)
            expect(7)
            delay(producerInterval)
        }

        val result = fastProducer.chunked(ChunkingMethod.Natural()).withIndex().onEach { indexed ->
            when (indexed.index) {
                0 -> expect(2)
                1 -> expect(5)
                2 -> finish(8)
            }
            delay(11)
        }.toList()

        assertEquals(3, result.size)
        assertEquals(1, result.first().value.size)
        for (i in 1..2) assertEquals(2, result[i].value.size)
    }

    @Test
    fun testEmptyFlowWithSlowTimeBasedChunking() = runTest {
        val emptyFlow = emptyFlow<Int>()
        val result = measureTimedValue { emptyFlow.chunked(ChunkingMethod.ByTime(intervalMs = 10 * 1000)).toList() }
        assertTrue(result.value.isEmpty())
        assertTrue(result.duration < 1000.milliseconds)
    }

    @Test
    fun testErrorPropagationInTimeBasedChunking() = runTest {
        val exception = IllegalArgumentException()
        val failedFlow = flow<Int> {
            emit(1)
            emit(2)
            throw exception
        }
        var catchedException: Throwable? = null

        val result = failedFlow
            .chunked(ChunkingMethod.ByTime(10 * 10_000))
            .catch { e ->
                catchedException = e
                emit(listOf(3))
            }
            .toList()

        assertTrue(catchedException is IllegalArgumentException)
        assertEquals(3, result.first().single())
    }

    @Test
    fun testTimeBasedChunkingOfMultipleElements() = withVirtualTime {
        val producer = flow<Int> {
            for (i in 1..10) {
                delay(1000)
                emit(i)
            }
        }

        val result = producer.chunked(ChunkingMethod.ByTime(5500)).toList()

        finish(1)

        assertEquals(2, result.size)
        assertEquals(5, result.first().size)
        assertEquals(5, result[1].size)
    }

    @Test
    fun testTimeBasedChunkingWithMaxChunkSizeSuspendingProducer() = runTest {
        val producer = flow<Int> {
            for (i in 1..10) {
                emit(i)
            }
        }

        val result = measureTimedValue { producer.chunked(ChunkingMethod.ByTime(200, maxSize = 5)).toList() }

        finish(1)

        assertEquals(2, result.value.size)
        assertEquals(5, result.value.first().size)
        assertEquals(5, result.value[1].size)
        assertTrue(result.duration >= 200.milliseconds, "expected time at least 400 ms but was: ${result.duration}")
    }

    @Test
    fun testEmptyFlowTimeOrSizeBasedChunking() = runTest {
        val emptyFlow = emptyFlow<Int>()
        val result = measureTimedValue {
            emptyFlow.chunked(ChunkingMethod.ByTimeOrSize(intervalMs = 10 * 1000, maxSize = 5)).toList()
        }
        assertTrue(result.value.isEmpty())
        assertTrue(result.duration < 500.milliseconds)
    }

    @Test
    fun testMultipleElementsFillingBufferWithTimeOrSizeBasedChunking() = runTest {
        val flow = flow<Int> {
            for (i in 1..10) {
                emit(i)
            }
        }
        val result = measureTimedValue {
            flow.chunked(ChunkingMethod.ByTimeOrSize(intervalMs = 10 * 1000, maxSize = 5)).toList()
        }
        assertEquals(2, result.value.size)
        assertEquals(5, result.value.first().size)
        assertEquals(5, result.value[1].size)
        assertTrue(result.duration < 500.milliseconds)
    }

    @Test
    fun testMultipleElementsNotFillingBufferWithTimeOrSizeBasedChunking() = runTest {
        val flow = flow<Int> {
            for (i in 1..10) {
                delay(10)
                emit(i)
            }
        }
        val result = measureTimedValue {
            flow.chunked(ChunkingMethod.ByTimeOrSize(intervalMs = 55, maxSize = 500)).toList()
        }

        assertEquals(2, result.value.size)
        assertEquals(5, result.value.first().size)
        assertEquals(5, result.value[1].size)
        assertTrue(result.duration >= 100.milliseconds)
    }

//    @Test
//    fun testEmptyFlowChunking() = runTest {
//        val emptyFlow = emptyFlow<Int>()
//        val result = measureTimedValue {
//            emptyFlow.chunked(10.seconds, ChunkConstraint.NO_MAXIMUM).toList()
//        }
//
//        assertTrue { result.value.isEmpty() }
//        assertTrue { result.duration.inSeconds < 1 }
//    }
//
//    @ExperimentalTime
//    @Test
//    fun testSingleFastElementChunking() = runTest {
//        val fastFlow = flow { emit(1) }
//
//        val result = measureTimedValue {
//            fastFlow.chunked(10.seconds, ChunkConstraint.NO_MAXIMUM).toList()
//        }
//
//        assertTrue { result.value.size == 1 && result.value.first().contains(1) }
//        assertTrue { result.duration.inSeconds < 1 }
//    }
//
//    @ExperimentalTime
//    @Test
//    fun testMultipleFastElementsChunking() = runTest {
//        val fastFlow = flow {
//            for(i in 1..1000) emit(1)
//        }
//
//        val result = measureTimedValue {
//            fastFlow.chunked(10.seconds, ChunkConstraint.NO_MAXIMUM).toList()
//        }
//
//        assertTrue { result.value.size == 1 && result.value.first().size == 1000 }
//        assertTrue { result.duration.inSeconds < 1 }
//    }
//
//    @Test
//    fun testRespectingSizeAndTimeLimit() = withVirtualTime {
//        val intervalFlow = flow {
//            delay(1500)
//            emit(1)
//            emit(2)
//            emit(3)
//            emit(4)
//            delay(1500)
//            emit(5)
//            delay(1500)
//            emit(6)
//        }
//        val chunks = intervalFlow.chunked(2.seconds, size = 3).toList()
//
//        assertEquals(3, chunks.size)
//        assertEquals(3, chunks.first().size)
//        assertEquals(2, chunks[1].size)
//        assertTrue { chunks[1].containsAll(listOf(4, 5)) }
//
//        finish(1)
//    }

}