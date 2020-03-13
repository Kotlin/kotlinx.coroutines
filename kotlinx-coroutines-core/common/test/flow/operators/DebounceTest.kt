/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*
import kotlin.time.*

class DebounceTest : TestBase() {
    @Test
    public fun testBasic() = withVirtualTime {
        expect(1)
        val flow = flow {
            expect(3)
            emit("A")
            delay(1500)
            emit("B")
            delay(500)
            emit("C")
            delay(250)
            emit("D")
            delay(2000)
            emit("E")
            expect(4)
        }

        expect(2)
        val result = flow.debounce(1000).toList()
        assertEquals(listOf("A", "D", "E"), result)
        finish(5)
    }

    @Test
    fun testSingleNull() = runTest {
        val flow = flowOf<Int?>(null).debounce(Long.MAX_VALUE)
        assertNull(flow.single())
    }

    @Test
    fun testBasicWithNulls() = withVirtualTime {
        expect(1)
        val flow = flow {
            expect(3)
            emit("A")
            delay(1500)
            emit("B")
            delay(500)
            emit("C")
            delay(250)
            emit(null)
            delay(2000)
            emit(null)
            expect(4)
        }

        expect(2)
        val result = flow.debounce(1000).toList()
        assertEquals(listOf("A", null, null), result)
        finish(5)
    }

    @Test
    fun testEmpty() = runTest {
        val flow = emptyFlow<Int>().debounce(Long.MAX_VALUE)
        assertNull(flow.singleOrNull())
    }

    @Test
    fun testScalar() = withVirtualTime {
        val flow = flowOf(1, 2, 3).debounce(1000)
        assertEquals(3, flow.single())
        finish(1)
    }

    @Test
    fun testPace() = withVirtualTime {
        val flow = flow {
            expect(1)
            repeat(10) {
                emit(-it)
                delay(99)
            }

            repeat(10) {
                emit(it)
                delay(101)
            }
            expect(2)
        }.debounce(100)

        assertEquals((0..9).toList(), flow.toList())
        finish(3)
    }

    @Test
    fun testUpstreamError()= testUpstreamError(TimeoutCancellationException(""))

    @Test
    fun testUpstreamErrorCancellation() = testUpstreamError(TimeoutCancellationException(""))

    private inline fun <reified T: Throwable> testUpstreamError(cause: T) = runTest {
        val latch = Channel<Unit>()
        val flow = flow {
            expect(1)
            emit(1)
            expect(2)
            latch.receive()
            throw cause
        }.debounce(1).map {
            latch.send(Unit)
            hang { expect(3) }
        }

        assertFailsWith<T>(flow)
        finish(4)
    }

    @Test
    fun testUpstreamErrorIsolatedContext() = runTest {
        val latch = Channel<Unit>()
        val flow = flow {
            assertEquals("upstream", NamedDispatchers.name())
            expect(1)
            emit(1)
            expect(2)
            latch.receive()
            throw TestException()
        }.flowOn(NamedDispatchers("upstream")).debounce(1).map {
            latch.send(Unit)
            hang { expect(3) }
        }

        assertFailsWith<TestException>(flow)
        finish(4)
    }

    @Test
    fun testUpstreamErrorDebounceNotTriggered() = runTest {
        val flow = flow {
            expect(1)
            emit(1)
            expect(2)
            throw TestException()
        }.debounce(Long.MAX_VALUE).map {
            expectUnreached()
        }
        assertFailsWith<TestException>(flow)
        finish(3)
    }

    @Test
    fun testUpstreamErrorDebounceNotTriggeredInIsolatedContext() = runTest {
        val flow = flow {
            expect(1)
            emit(1)
            expect(2)
            throw TestException()
        }.flowOn(NamedDispatchers("source")).debounce(Long.MAX_VALUE).map {
                expectUnreached()
        }
        assertFailsWith<TestException>(flow)
        finish(3)
    }

    @Test
    fun testDownstreamError() = runTest {
        val flow = flow {
            expect(1)
            emit(1)
            hang { expect(3) }
        }.debounce(100).map {
            expect(2)
            yield()
            throw TestException()
            it
        }

        assertFailsWith<TestException>(flow)
        finish(4)
    }

    @Test
    fun testDownstreamErrorIsolatedContext() = runTest {
        val flow = flow {
            assertEquals("upstream", NamedDispatchers.name())
            expect(1)
            emit(1)
            hang { expect(3) }
        }.flowOn(NamedDispatchers("upstream")).debounce(100).map {
            expect(2)
            yield()
            throw TestException()
            it
        }

        assertFailsWith<TestException>(flow)
        finish(4)
    }

    @ExperimentalTime
    @Test
    public fun testDurationBasic() = withVirtualTime {
        expect(1)
        val flow = flow {
            expect(3)
            emit("A")
            delay(1500.milliseconds)
            emit("B")
            delay(500.milliseconds)
            emit("C")
            delay(250.milliseconds)
            emit("D")
            delay(2000.milliseconds)
            emit("E")
            expect(4)
        }

        expect(2)
        val result = flow.debounce(1000.milliseconds).toList()
        assertEquals(listOf("A", "D", "E"), result)
        finish(5)
    }
}
