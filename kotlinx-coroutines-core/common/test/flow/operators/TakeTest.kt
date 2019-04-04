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
}
