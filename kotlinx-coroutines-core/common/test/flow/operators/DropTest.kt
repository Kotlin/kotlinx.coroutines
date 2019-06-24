/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class DropTest : TestBase() {
    @Test
    fun testDrop() = runTest {
        val flow = flow {
            emit(1)
            emit(2)
            emit(3)
        }

        assertEquals(5, flow.drop(1).sum())
        assertEquals(0, flow.drop(Int.MAX_VALUE).sum())
        assertNull(flow.drop(Int.MAX_VALUE).singleOrNull())
        assertEquals(3, flow.drop(1).take(2).drop(1).single())
    }

    @Test
    fun testEmptyFlow() = runTest {
        assertEquals(0, flowOf<Int>().drop(1).sum())
    }

    @Test
    fun testNegativeCount() {
        assertFailsWith<IllegalArgumentException> {
            emptyFlow<Int>().drop(-1)
        }
    }

    @Test
    fun testErrorCancelsUpstream() = runTest {
        val flow = flow {
            coroutineScope {
                launch(start = CoroutineStart.ATOMIC) {
                    hang { expect(5) }
                }
                expect(2)
                emit(1)
                expect(3)
                emit(2)
                expectUnreached()
            }
        }.drop(1)
            .map {
                expect(4)
                throw TestException()
                42
            }.catch { emit(42) }

        expect(1)
        assertEquals(42, flow.single())
        finish(6)
    }
}
