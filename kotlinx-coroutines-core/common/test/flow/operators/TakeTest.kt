/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class TakeTest : TestBase() {
    @Test
    fun testTake() = runTest {
        val flow = flow {
            emit(1)
            emit(2)
        }

        assertEquals(3, flow.take(2).sum())
        assertEquals(3, flow.take(Int.MAX_VALUE).sum())
        assertEquals(1, flow.take(1).single())
        assertEquals(2, flow.drop(1).take(1).single())
    }

    @Test
    fun testEmptyFlow() = runTest {
        val sum = emptyFlow<Int>().take(10).sum()
        assertEquals(0, sum)
    }

    @Test
    fun testNonPositiveValues() {
        val flow = flowOf(1)
        assertFailsWith<IllegalArgumentException> {
            flow.take(-1)
        }

        assertFailsWith<IllegalArgumentException> {
            flow.take(0)
        }
    }

    @Test
    fun testCancelUpstream() = runTest {
        var cancelled = false
        val flow = flow {
            coroutineScope {
                launch(start = CoroutineStart.ATOMIC) {
                    hang { cancelled = true }
                }

                emit(1)
            }
        }

        assertEquals(1, flow.take(1).single())
        assertTrue(cancelled)
    }

    @Test
    fun testErrorCancelsUpstream() = runTest {
        var cancelled = false
        val flow = flow {
            coroutineScope {
                launch(start = CoroutineStart.ATOMIC) {
                    hang { cancelled = true }
                }
                emit(1)
            }
        }.take(2)
            .map {
                throw TestException()
                42
            }.onErrorReturn(42)

        assertEquals(42, flow.single())
        assertTrue(cancelled)
    }

    @Test
    fun takeWithRetries() = runTest {
        val flow = flow {
            expect(1)
            emit(1)
            expect(2)
            emit(2)

            while (true) {
                emit(42)
                expectUnreached()
            }

        }.retry(2) {
            expectUnreached()
            true
        }.take(2)

        val sum = flow.sum()
        assertEquals(3, sum)
        finish(3)
    }

    @Test
    fun testNonIdempotentRetry() = runTest {
        var count = 0
        flow { while (true) emit(1) }
            .retry { count++ % 2 != 0 }
            .take(1)
            .collect {
                expect(1)
            }
        finish(2)
    }
}
