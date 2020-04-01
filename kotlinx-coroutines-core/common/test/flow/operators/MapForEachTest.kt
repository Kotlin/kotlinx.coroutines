/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.TestBase
import kotlinx.coroutines.TestException
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.hang
import kotlinx.coroutines.launch
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class MapForEachTest : TestBase() {
    @Test
    fun testMap() = runTest {
        val flow = flow {
            emit(listOf(1, 2))
        }

        val result = flow.mapForEach { it + 1 }.single()
        val expectedList = listOf(2, 3)
        assertEquals(expectedList, result)
    }

    @Test
    fun testEmptyFlow() = runTest {
        val result = emptyFlow<List<Int>>().mapForEach { expectUnreached(); it }.singleOrNull() ?: emptyList()
        assertEquals(emptyList(), result)
    }

    @Test
    fun testErrorCancelsUpstream() = runTest {
        var cancelled = false
        val latch = Channel<Unit>()
        val flow = flow {
            coroutineScope {
                launch {
                    latch.send(Unit)
                    hang { cancelled = true }
                }
                emit(listOf(1))
            }
        }.mapForEach {
            latch.receive()
            throw TestException()
            it + 1
        }.catch { emit(listOf(42)) }

        assertEquals(listOf(42), flow.single())
        assertTrue(cancelled)
    }
}