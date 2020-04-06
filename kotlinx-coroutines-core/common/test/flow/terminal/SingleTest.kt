/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class SingleTest : TestBase() { 

    @Test
    fun testSingle() = runTest {
        val flow = flow {
            emit(239L)
        }

        assertEquals(239L, flow.single())
        assertEquals(239L, flow.singleOrNull())
    }

    @Test
    fun testMultipleValues() = runTest {
        val flow = flow {
            emit(239L)
            emit(240L)
        }
        assertFailsWith<RuntimeException> { flow.single() }
        assertFailsWith<RuntimeException> { flow.singleOrNull() }
    }

    @Test
    fun testNoValues() = runTest {
        assertFailsWith<NoSuchElementException> { flow<Int> {}.single() }
        assertNull(flow<Int> {}.singleOrNull())
    }

    @Test
    fun testException() = runTest {
        val flow = flow<Int> {
            throw TestException()
        }

        assertFailsWith<TestException> { flow.single() }
        assertFailsWith<TestException> { flow.singleOrNull() }
    }

    @Test
    fun testExceptionAfterValue() = runTest {
        val flow = flow {
            emit(1)
            throw TestException()
        }

        assertFailsWith<TestException> { flow.single() }
        assertFailsWith<TestException> { flow.singleOrNull() }
    }

    @Test
    fun testNullableSingle() = runTest {
        assertEquals(1, flowOf<Int?>(1).single())
        assertNull(flowOf<Int?>(null).single())
        assertFailsWith<NoSuchElementException> { flowOf<Int?>().single() }
    }

    @Test
    fun testBadClass() = runTest {
        val instance = BadClass()
        val flow = flowOf(instance)
        assertSame(instance, flow.single())
        assertSame(instance, flow.singleOrNull())
    }
}
