/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.test.*
import kotlin.coroutines.coroutineContext as currentContext

class FlowContextOptimizationsTest : TestBase() {
    @Test
    fun testBaseline() = runTest {
        val flowDispatcher = wrapperDispatcher(currentContext)
        val collectContext = currentContext
        flow {
            assertSame(flowDispatcher, currentContext[ContinuationInterceptor] as CoroutineContext)
            expect(1)
            emit(1)
            expect(2)
            emit(2)
            expect(3)
        }
            .flowOn(flowDispatcher)
            .collect { value ->
                assertEquals(collectContext.minusKey(Job), currentContext.minusKey(Job))
                if (value == 1) expect(4)
                else expect(5)
            }

        finish(6)
    }

    @Test
    fun testFusedSameContext() = runTest {
        flow {
            expect(1)
            emit(1)
            expect(3)
            emit(2)
            expect(5)
        }
            .flowOn(currentContext.minusKey(Job))
            .collect { value ->
                if (value == 1) expect(2)
                else expect(4)
            }
        finish(6)
    }

    @Test
    fun testFusedSameContextWithIntermediateOperators() = runTest {
        flow {
            expect(1)
            emit(1)
            expect(3)
            emit(2)
            expect(5)
        }
            .flowOn(currentContext.minusKey(Job))
            .map { it }
            .flowOn(currentContext.minusKey(Job))
            .collect { value ->
                if (value == 1) expect(2)
                else expect(4)
            }
        finish(6)
    }

    @Test
    fun testFusedSameDispatcher() = runTest {
        flow {
            assertEquals("Name", currentContext[CoroutineName]?.name)
            expect(1)
            emit(1)
            expect(3)
            emit(2)
            expect(5)
        }
            .flowOn(CoroutineName("Name"))
            .collect { value ->
                assertEquals(null, currentContext[CoroutineName]?.name)
                if (value == 1) expect(2)
                else expect(4)
            }
        finish(6)
    }

    @Test
    fun testFusedManySameDispatcher() = runTest {
        flow {
            assertEquals("Name1", currentContext[CoroutineName]?.name)
            assertEquals("OK", currentContext[CustomContextElement]?.str)
            expect(1)
            emit(1)
            expect(3)
            emit(2)
            expect(5)
        }
            .flowOn(CoroutineName("Name1")) // the first one works
            .flowOn(CoroutineName("Name2"))
            .flowOn(CoroutineName("Name3") + CustomContextElement("OK")) // but this is not lost
            .collect { value ->
                assertEquals(null, currentContext[CoroutineName]?.name)
                assertEquals(null, currentContext[CustomContextElement]?.str)
                if (value == 1) expect(2)
                else expect(4)
            }
        finish(6)
    }

    data class CustomContextElement(val str: String) : AbstractCoroutineContextElement(Key) {
        companion object Key : CoroutineContext.Key<CustomContextElement>
    }
}
