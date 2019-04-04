/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class FilterTrivialTest : TestBase() {

    @Test
    fun testFilterNotNull() = runTest {
        val flow = flowOf(1, 2, null)
        assertEquals(3, flow.filterNotNull().sum())
    }

    @Test
    fun testEmptyFlowNotNull() = runTest {
        val sum = emptyFlow<Int?>().filterNotNull().sum()
        assertEquals(0, sum)
    }

    @Test
    fun testFilterIsInstance() = runTest {
        val flow = flowOf("value", 2.0)
        assertEquals(2.0, flow.filterIsInstance<Double>().single())
        assertEquals("value", flow.filterIsInstance<String>().single())
    }

    @Test
    fun testFilterIsInstanceNullable() = runTest {
        val flow = flowOf(1, 2, null)
        assertEquals(2, flow.filterIsInstance<Int>().count())
        assertEquals(3, flow.filterIsInstance<Int?>().count())
    }

    @Test
    fun testEmptyFlowIsInstance() = runTest {
        val sum = emptyFlow<Int>().filterIsInstance<Int>().sum()
        assertEquals(0, sum)
    }
}
