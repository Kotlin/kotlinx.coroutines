/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class DropWhileTest : TestBase() {
    @Test
    fun testDropWhile() = runTest {
        val flow = flow {
            emit(1)
            emit(2)
            emit(3)
        }

        assertEquals(6, flow.dropWhile { false }.sum())
        assertNull(flow.dropWhile { true }.singleOrNull())
        assertEquals(5, flow.dropWhile { it < 2 }.sum())
        assertEquals(1, flow.take(1).dropWhile { it > 1 }.single())
    }

    @Test
    fun testEmptyFlow() = runTest {
        assertEquals(0, flowOf<Int>().dropWhile { true }.sum())
        assertEquals(0, flowOf<Int>().dropWhile { false }.sum())
    }

    @Test
    fun testErrorCancelsUpstream() = runTest {
        val flow = flow {
            coroutineScope {
                launch(start = CoroutineStart.ATOMIC) {
                    hang { expect(4) }
                }
                expect(2)
                emit(1)
                expectUnreached()
            }
        }.dropWhile {
            expect(3)
            throw TestException()
        }

        expect(1)
        assertFailsWith<TestException>(flow)
        finish(5)
    }
}
