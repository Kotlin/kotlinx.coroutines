/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class TakeWhileTest : TestBase() {

    @Test
    fun testTakeWhile() = runTest {
        val flow = flow {
            emit(1)
            emit(2)
        }

        assertEquals(3, flow.takeWhile { true }.sum())
        assertEquals(1, flow.takeWhile { it < 2 }.single())
        assertEquals(2, flow.drop(1).takeWhile { it < 3 }.single())
        assertNull(flow.drop(1).takeWhile { it < 2 }.singleOrNull())
    }

    @Test
    fun testEmptyFlow() = runTest {
        assertEquals(0, emptyFlow<Int>().takeWhile { true }.sum())
        assertEquals(0, emptyFlow<Int>().takeWhile { false }.sum())
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
                emit(2)
            }
        }

        assertEquals(1, flow.takeWhile { it < 2 }.single())
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
        }.takeWhile {
            throw TestException()
        }

        assertFailsWith<TestException>(flow)
        assertTrue(cancelled)
        assertEquals(42, flow.catch { emit(42) }.single())
    }
}
