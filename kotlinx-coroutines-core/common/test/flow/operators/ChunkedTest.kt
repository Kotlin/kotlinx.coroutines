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
    fun testEmptyFlowChunking() = runTest {
        val emptyFlow = emptyFlow<Int>()
        val result = measureTimedValue {
            emptyFlow.chunked(10.seconds).toList()
        }

        assertTrue { result.value.isEmpty() }
        assertTrue { result.duration.inSeconds < 1 }
    }

    @ExperimentalTime
    @Test
    fun testSingleFastElementChunking() = runTest {
        val fastFlow = flow { emit(1) }

        val result = measureTimedValue {
            fastFlow.chunked(10.seconds).toList()
        }

        assertTrue { result.value.size == 1 && result.value.first().contains(1) }
        assertTrue { result.duration.inSeconds < 1 }
    }

    @ExperimentalTime
    @Test
    fun testMultipleFastElementsChunking() = runTest {
        val fastFlow = flow {
            for(i in 1..1000) emit(1)
        }

        val result = measureTimedValue {
            fastFlow.chunked(10.seconds).toList()
        }

        assertTrue { result.value.size == 1 && result.value.first().size == 1000 }
        assertTrue { result.duration.inSeconds < 1 }
    }

    @Test
    fun testFixedTimeWindowChunkingWithZeroMinimumSize() = withVirtualTime {
        val intervalFlow = flow {
            delay(1500)
            emit(1)
            delay(1500)
            emit(2)
            delay(1500)
            emit(3)
        }
        val chunks = intervalFlow.chunked(2.seconds, minSize = 0).toList()

        assertEquals (3, chunks.size)
        assertTrue { chunks.all { it.size == 1 } }

        finish(1)
    }

    @Test
    fun testDefaultChunkingWithFloatingWindows() = withVirtualTime {
        val intervalFlow = flow {
            delay(1500)
            emit(1)
            delay(1500)
            emit(2)
            delay(1500)
            emit(3)
        }
        val chunks = intervalFlow.chunked(2.seconds).toList()

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
        val chunks = intervalFlow.chunked(2.seconds, minSize = 3).toList()

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
        val chunks = intervalFlow.chunked(2.seconds, minSize = 0, maxSize = 3).toList()

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
        val chunks = intervalFlow.chunked(2.seconds, maxSize = 3).toList()

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