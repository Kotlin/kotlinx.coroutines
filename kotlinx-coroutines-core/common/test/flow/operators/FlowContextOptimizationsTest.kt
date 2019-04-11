/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.test.*

class FlowContextOptimizationsTest : TestBase() {

    @Test
    fun testBaseline() = runTest {
        val flowDispatcher = wrapperDispatcher(coroutineContext)
        val collectContext = coroutineContext
        flow {
            assertSame(flowDispatcher, kotlin.coroutines.coroutineContext[ContinuationInterceptor] as CoroutineContext)
            expect(1)
            emit(1)
            expect(2)
            emit(2)
            expect(3)
        }.flowOn(flowDispatcher)
            .collect { value ->
                assertEquals(collectContext, coroutineContext)
                if (value == 1) expect(4)
                else expect(5)
            }

        finish(6)
    }

    @Test
    fun testFusable() = runTest {
        flow {
            expect(1)
            emit(1)
            expect(3)
            emit(2)
            expect(5)
        }.flowOn(coroutineContext.minusKey(Job))
            .collect { value ->
                if (value == 1) expect(2)
                else expect(4)
            }

        finish(6)
    }

    @Test
    fun testFusableWithIntermediateOperators() = runTest {
        flow {
            expect(1)
            emit(1)
            expect(3)
            emit(2)
            expect(5)
        }.flowOn(coroutineContext.minusKey(Job))
            .map { it }
            .flowOn(coroutineContext.minusKey(Job))
            .collect { value ->
                if (value == 1) expect(2)
                else expect(4)
            }

        finish(6)
    }

    @Test
    fun testNotFusableWithContext() = runTest {
        flow {
            expect(1)
            emit(1)
            expect(2)
            emit(2)
            expect(3)
        }.flowOn(coroutineContext.minusKey(Job) + CoroutineName("Name"))
            .collect { value ->
                if (value == 1) expect(4)
                else expect(5)
            }

        finish(6)
    }

    @Test
    fun testFusableFlowWith() = runTest {
        flow {
            expect(1)
            emit(1)
            expect(4)
        }.flowWith(coroutineContext.minusKey(Job)) {
            onEach { value ->
                expect(2)
            }
        }.collect {
            expect(3)
        }

        finish(5)
    }
}
