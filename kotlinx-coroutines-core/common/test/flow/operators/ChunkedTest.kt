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
            emptyFlow.chunked(10.seconds, ChunkConstraint.NO_MAXIMUM).toList()
        }

        assertTrue { result.value.isEmpty() }
        assertTrue { result.duration.inSeconds < 1 }
    }

    @ExperimentalTime
    @Test
    fun testSingleFastElementChunking() = runTest {
        val fastFlow = flow { emit(1) }

        val result = measureTimedValue {
            fastFlow.chunked(10.seconds, ChunkConstraint.NO_MAXIMUM).toList()
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
            fastFlow.chunked(10.seconds, ChunkConstraint.NO_MAXIMUM).toList()
        }

        assertTrue { result.value.size == 1 && result.value.first().size == 1000 }
        assertTrue { result.duration.inSeconds < 1 }
    }

    @Test
    fun testRespectingSizeAndTimeLimit() = withVirtualTime {
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
        val chunks = intervalFlow.chunked(2.seconds, size = 3).toList()

        assertEquals(3, chunks.size)
        assertEquals(3, chunks.first().size)
        assertEquals(2, chunks[1].size)
        assertTrue { chunks[1].containsAll(listOf(4, 5)) }

        finish(1)
    }

}