/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class IndexedTest : TestBase() {

    @Test
    fun testWithIndex() = runTest {
        val flow = flowOf(3, 2, 1).withIndex()
        assertEquals(listOf(IndexedValue(0, 3), IndexedValue(1, 2), IndexedValue(2, 1)), flow.toList())
    }

    @Test
    fun testWithIndexEmpty() = runTest {
        val flow = emptyFlow<Int>().withIndex()
        assertEquals(emptyList(), flow.toList())
    }

    @Test
    fun testCollectIndexed() = runTest {
        val result = ArrayList<IndexedValue<Long>>()
        flowOf(3L, 2L, 1L).collectIndexed { index, value ->
            result.add(IndexedValue(index, value))
        }
        assertEquals(listOf(IndexedValue(0, 3L), IndexedValue(1, 2L), IndexedValue(2, 1L)), result)
    }

    @Test
    fun testCollectIndexedEmptyFlow() = runTest {
        val flow = flow<Int> {
            expect(1)
        }

        flow.collectIndexed { _, _ ->
            expectUnreached()
        }

        finish(2)
    }
}
