/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class FirstTest : TestBase() {
    @Test
    fun testFirst() = runTest {
        val flow = flowOf(1, 2, 3)
        assertEquals(1, flow.first())
    }

    @Test
    fun testNulls() = runTest {
        val flow = flowOf(null, 1)
        assertNull(flow.first())
        assertNull(flow.first { it == null })
        assertEquals(1, flow.first { it != null })
    }

    @Test
    fun testFirstWithPredicate() = runTest {
        val flow = flowOf(1, 2, 3)
        assertEquals(1, flow.first { it > 0 })
        assertEquals(2, flow.first { it > 1 })
        assertFailsWith<NoSuchElementException> { flow.first { it > 3 } }
    }

    @Test
    fun testFirstCancellation() = runTest {
        val latch = Channel<Unit>()
        val flow = flow {
            coroutineScope {
                launch {
                    latch.send(Unit)
                    hang { expect(1) }
                }
                emit(1)
                emit(2)
            }
        }


        val result = flow.first {
            latch.receive()
            true
        }
        assertEquals(1, result)
        finish(2)
    }

    @Test
    fun testEmptyFlow() = runTest {
        assertFailsWith<NoSuchElementException> { emptyFlow<Int>().first() }
        assertFailsWith<NoSuchElementException> { emptyFlow<Int>().first { true } }
    }

    @Test
    fun testErrorCancelsUpstream() = runTest {
        val latch = Channel<Unit>()
        val flow = flow {
            coroutineScope {
                launch {
                    latch.send(Unit)
                    hang { expect(1) }
                }
                emit(1)
            }
        }

        assertFailsWith<TestException> {
            flow.first {
                latch.receive()
                throw TestException()
            }
        }

        assertEquals(1, flow.first())
        finish(2)
    }

    @Test
    fun testFirstOrNull() = runTest {
        val flow = flowOf(1, 2, 3)
        assertEquals(1, flow.firstOrNull())
    }

    @Test
    fun testFirstOrNullWithPredicate() = runTest {
        val flow = flowOf(1, 2, 3)
        assertEquals(1, flow.firstOrNull { it > 0 })
        assertEquals(2, flow.firstOrNull { it > 1 })
        assertNull(flow.firstOrNull { it > 3 })
    }

    @Test
    fun testFirstOrNullCancellation() = runTest {
        val latch = Channel<Unit>()
        val flow = flow {
            coroutineScope {
                launch {
                    latch.send(Unit)
                    hang { expect(1) }
                }
                emit(1)
                emit(2)
            }
        }


        val result = flow.firstOrNull {
            latch.receive()
            true
        }
        assertEquals(1, result)
        finish(2)
    }

    @Test
    fun testFirstOrNullWithEmptyFlow() = runTest {
        assertNull(emptyFlow<Int>().firstOrNull())
        assertNull(emptyFlow<Int>().firstOrNull { true })
    }

    @Test
    fun testFirstOrNullWhenErrorCancelsUpstream() = runTest {
        val latch = Channel<Unit>()
        val flow = flow {
            coroutineScope {
                launch {
                    latch.send(Unit)
                    hang { expect(1) }
                }
                emit(1)
            }
        }

        assertFailsWith<TestException> {
            flow.firstOrNull {
                latch.receive()
                throw TestException()
            }
        }

        assertEquals(1, flow.firstOrNull())
        finish(2)
    }

    @Test
    fun testBadClass() = runTest {
        val instance = BadClass()
        val flow = flowOf(instance)
        assertSame(instance, flow.first())
        assertSame(instance, flow.firstOrNull())
        assertSame(instance, flow.first { true })
        assertSame(instance, flow.firstOrNull { true })
    }
}
