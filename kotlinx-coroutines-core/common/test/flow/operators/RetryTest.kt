/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class RetryTest : TestBase() {
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
}