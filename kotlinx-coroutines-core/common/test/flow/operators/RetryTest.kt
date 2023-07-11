/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class RetryTest : TestBase() {
    @Test
    fun testRetryWhen() = runTest {
        expect(1)
        val flow = flow {
            emit(1)
            throw TestException()
        }
        val sum = flow.retryWhen { cause, attempt ->
            assertTrue(cause is TestException)
            expect(2 + attempt.toInt())
            attempt < 3
        }.catch { cause ->
            expect(6)
            assertTrue(cause is TestException)
        }.sum()
        assertEquals(4, sum)
        finish(7)
    }

    @Test
    fun testRetry() = runTest {
        var counter = 0
        val flow = flow {
            emit(1)
            if (++counter < 4) throw TestException()
        }

        assertEquals(4, flow.retry(4).sum())
        counter = 0
        assertFailsWith<TestException>(flow)
        counter = 0
        assertFailsWith<TestException>(flow.retry(2))
    }

    @Test
    fun testRetryPredicate() = runTest {
        var counter = 0
        val flow = flow {
            emit(1);
            if (++counter == 1) throw TestException()
        }

        assertEquals(2, flow.retry(1) { it is TestException }.sum())
        counter = 0
        assertFailsWith<TestException>(flow.retry(1) { it !is TestException })
    }

    @Test
    fun testRetryExceptionFromDownstream() = runTest {
        var executed = 0
        val flow = flow {
            emit(1)
        }.retry(42).map {
            ++executed
            throw TestException()
        }

        assertFailsWith<TestException>(flow)
        assertEquals(1, executed)
    }

    @Test
    fun testWithTimeoutRetried() = runTest {
        var state = 0
        val flow = flow {
            if (state++ == 0) {
                expect(1)
                withTimeout(1) {
                    hang { expect(2) }
                }
                expectUnreached()
            }
            expect(3)
            emit(1)
        }.retry(1)

        assertEquals(1, flow.single())
        finish(4)
    }

    @Test
    fun testCancellationFromUpstreamIsNotRetried() = runTest {
        val flow = flow<Int> {
            hang {  }
        }.retry()

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
    fun testUpstreamExceptionConcurrentWithDownstream() = runTest {
        val flow = flow {
            try {
                expect(1)
                emit(1)
            } finally {
                expect(3)
                throw TestException()
            }
        }.retry { expectUnreached(); true }.onEach {
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
        }.retry { expectUnreached(); true }.onEach {
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
        }.retry { expectUnreached(); true }.onEach {
            expect(2)
            throw TestException("")
        }

        assertFailsWith<TestException>(flow)
        finish(4)
    }
}
