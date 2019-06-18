/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class CatchTest : TestBase() {
    @Test
    fun testCatchEmit() = runTest {
        val flow = flow {
            emit(1)
            throw TestException()
        }

        assertEquals(42, flow.catch { emit(41) }.sum())
        assertFailsWith<TestException>(flow)
    }

    @Test
    fun testCatchEmitExceptionFromDownstream() = runTest {
        var executed = 0
        val flow = flow {
            emit(1)
        }.catch { emit(42) }.map {
            ++executed
            throw TestException()
        }

        assertFailsWith<TestException>(flow)
        assertEquals(1, executed)
    }

    @Test
    fun testCatchEmitAll() = runTest {
        val flow = flow {
            emit(1)
            throw TestException()
        }.catch { emitAll(flowOf(2)) }

        assertEquals(3, flow.sum())
    }

    @Test
    fun testCatchEmitAllExceptionFromDownstream() = runTest {
        var executed = 0
        val flow = flow {
            emit(1)
        }.catch { emitAll(flowOf(1, 2, 3)) }.map {
            ++executed
            throw TestException()
        }

        assertFailsWith<TestException>(flow)
        assertEquals(1, executed)
    }

    @Test
    fun testWithTimeoutCatch() = runTest {
        val flow = flow<Int> {
            withTimeout(1) {
                hang { expect(1) }
            }
            expectUnreached()
        }.catch { emit(1) }

        assertEquals(1, flow.single())
        finish(2)
    }

    @Test
    fun testCancellationFromUpstreamCatch() = runTest {
        val flow = flow<Int> {
            hang {  }
        }.catch { expectUnreached() }

        val job = launch {
            expect(1)
            flow.collect {  }
        }

        yield()
        expect(2)
        job.cancelAndJoin()
        finish(3)
    }
}
