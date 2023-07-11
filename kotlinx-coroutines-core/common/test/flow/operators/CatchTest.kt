/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.coroutines.*
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

    @Test
    fun testCatchContext() = runTest {
        expect(1)
        val flow = flow {
            expect(2)
            emit("OK")
            expect(3)
            throw TestException()
        }
        val d0 = coroutineContext[ContinuationInterceptor] as CoroutineContext
        val d1 = wrapperDispatcher(coroutineContext)
        val d2 = wrapperDispatcher(coroutineContext)
        flow
            .catch { e ->
                expect(4)
                assertTrue(e is TestException)
                assertEquals("A", kotlin.coroutines.coroutineContext[CoroutineName]?.name)
                assertSame(d1, kotlin.coroutines.coroutineContext[ContinuationInterceptor] as CoroutineContext)
                throw e // rethrow downstream
            }
            .flowOn(CoroutineName("A"))
            .catch { e ->
                expect(5)
                assertTrue(e is TestException)
                assertEquals("B", kotlin.coroutines.coroutineContext[CoroutineName]?.name)
                assertSame(d1, kotlin.coroutines.coroutineContext[ContinuationInterceptor] as CoroutineContext)
                throw e // rethrow downstream
            }
            .flowOn(CoroutineName("B"))
            .catch { e ->
                expect(6)
                assertTrue(e is TestException)
                assertSame(d1, kotlin.coroutines.coroutineContext[ContinuationInterceptor] as CoroutineContext)
                throw e // rethrow downstream
            }
            .flowOn(d1)
            .catch { e ->
                expect(7)
                assertTrue(e is TestException)
                assertSame(d2, kotlin.coroutines.coroutineContext[ContinuationInterceptor] as CoroutineContext)
                throw e // rethrow downstream
            }
            .flowOn(d2)
            // flowOn with a different dispatcher introduces asynchrony so that all exceptions in the
            // upstream flows are handled before they go downstream
            .onEach {
                expectUnreached() // already cancelled
            }
            .catch { e ->
                expect(8)
                assertTrue(e is TestException)
                assertSame(d0, kotlin.coroutines.coroutineContext[ContinuationInterceptor] as CoroutineContext)
            }
            .collect()
        finish(9)
    }

    @Test
    fun testUpstreamExceptionConcurrentWithDownstream() = runTest {
        val flow = flow {
            try {
                expect(1)
                emit(1)
            } finally {
                expect(3)
                throw TestException()
            }
        }.catch { expectUnreached() }.onEach {
            expect(2)
            throw TestException2()
        }

        assertFailsWith<TestException>(flow)
        finish(4)
    }

    @Test
    fun testUpstreamExceptionConcurrentWithDownstreamCancellation() = runTest {
        val flow = flow {
            try {
                expect(1)
                emit(1)
            } finally {
                expect(3)
                throw TestException()
            }
        }.catch { expectUnreached() }.onEach {
            expect(2)
            throw CancellationException("")
        }

        assertFailsWith<TestException>(flow)
        finish(4)
    }

    @Test
    fun testUpstreamCancellationIsIgnoredWhenDownstreamFails() = runTest {
        val flow = flow {
            try {
                expect(1)
                emit(1)
            } finally {
                expect(3)
                throw CancellationException("")
            }
        }.catch { expectUnreached() }.onEach {
            expect(2)
            throw TestException("")
        }

        assertFailsWith<TestException>(flow)
        finish(4)
    }
}
