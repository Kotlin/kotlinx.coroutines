/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.operators

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.test.*

class OnEmptyTest : TestBase() {

    @Test
    fun testOnEmptyInvoked() = runTest {
        val flow = emptyFlow<Int>().onEmpty { emit(1) }
        assertEquals(1, flow.single())
    }

    @Test
    fun testOnEmptyNotInvoked() = runTest {
        val flow = flowOf(1).onEmpty { emit(2) }
        assertEquals(1, flow.single())
    }

    @Test
    fun testOnEmptyNotInvokedOnError() = runTest {
        val flow = flow<Int> {
            throw TestException()
        }.onEmpty { expectUnreached() }
        assertFailsWith<TestException>(flow)
    }

    @Test
    fun testOnEmptyNotInvokedOnCancellation() = runTest {
        val flow = flow<Int> {
            expect(2)
            hang { expect(4) }
        }.onEmpty { expectUnreached() }

        expect(1)
        val job = flow.onEach { expectUnreached() }.launchIn(this)
        yield()
        expect(3)
        job.cancelAndJoin()
        finish(5)
    }

    @Test
    fun testOnEmptyCancellation() = runTest {
        val flow = emptyFlow<Int>().onEmpty {
            expect(2)
            hang { expect(4) }
            emit(1)
        }
        expect(1)
        val job = flow.onEach { expectUnreached() }.launchIn(this)
        yield()
        expect(3)
        job.cancelAndJoin()
        finish(5)
    }

    @Test
    fun testTransparencyViolation() = runTest {
        val flow = emptyFlow<Int>().onEmpty {
            expect(2)
            coroutineScope {
                launch {
                    try {
                        emit(1)
                    } catch (e: IllegalStateException) {
                        expect(3)
                    }
                }
            }
        }
        expect(1)
        assertNull(flow.singleOrNull())
        finish(4)
    }
}
