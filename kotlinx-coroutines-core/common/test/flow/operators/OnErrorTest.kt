/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class OnErrorTest : TestBase() {
    @Test
    fun testOnErrorReturn() = runTest {
        val flow = flow {
            emit(1)
            throw TestException()
        }

        assertEquals(42, flow.onErrorReturn(41).sum())
        assertFailsWith<TestException>(flow)
    }

    @Test
    fun testOnErrorReturnPredicate() = runTest {
        val flow = flow { emit(1); throw TestException() }
        assertFailsWith<TestException>(flow.onErrorReturn(42) { it !is TestException })
    }

    @Test
    fun testOnErrorReturnExceptionFromDownstream() = runTest {
        var executed = 0
        val flow = flow {
            emit(1)
        }.onErrorReturn(42).map {
            ++executed
            throw TestException()
        }

        assertFailsWith<TestException>(flow)
        assertEquals(1, executed)
    }

    @Test
    fun testOnErrorCollect() = runTest {
        val flow = flow {
            emit(1)
            throw TestException()
        }.onErrorCollect(flowOf(2))

        assertEquals(3, flow.sum())
    }

    @Test
    fun testOnErrorCollectPredicate() = runTest {
        val flow = flow { emit(1); throw TestException() }
        assertFailsWith<TestException>(flow.onErrorCollect(flowOf(2)) { it !is TestException })
    }

    @Test
    fun testOnErrorCollectExceptionFromDownstream() = runTest {
        var executed = 0
        val flow = flow {
            emit(1)
        }.onErrorCollect(flowOf(1, 2, 3)).map {
            ++executed
            throw TestException()
        }

        assertFailsWith<TestException>(flow)
        assertEquals(1, executed)
    }

    @Test
    fun testWithTimeoutOnError() = runTest {
        val flow = flow<Int> {
            withTimeout(1) {
                hang { expect(1) }
            }
            expectUnreached()
        }.onErrorReturn(1)

        assertEquals(1, flow.single())
        finish(2)
    }

    @Test
    fun testCancellationFromUpstreamOnError() = runTest {
        val flow = flow<Int> {
            hang {  }
        }.onErrorCollect(flow { expectUnreached() })

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
