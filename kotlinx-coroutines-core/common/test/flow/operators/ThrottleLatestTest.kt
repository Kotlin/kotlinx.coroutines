/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*
import kotlin.time.*

class ThrottleLatestTest : TestBase() {

    @Test
    fun testBasic() = withVirtualTime {
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
        val result = flow.throttleLatest(1000).toList()
        assertEquals(listOf("A", "B", "D", "E"), result)
        finish(5)
    }

    @Test
    fun testSingleNull() = runTest {
        val flow = flowOf<Int?>(null).throttleLatest(Long.MAX_VALUE)
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
        val result = flow.throttleLatest(1000).toList()
        assertEquals(listOf("A", "B", null, null), result)
        finish(5)
    }

    @Test
    fun testSlidingWindow() = withVirtualTime {
        val flow = flow {
            expect(1)
            emit("A")
            delay(500)
            emit("B")
            delay(750)
            emit("C")
            delay(250)
            emit("D")
            delay(1000)
            emit("E")
            delay(250)
            emit("F")
            delay(1500)
            emit("G")
            expect(2)
        }

        val result = flow.throttleLatest(1000).toList()
        assertEquals(listOf("A", "B", "D", "F", "G"), result)
        finish(3)
    }

    @Test
    fun testDelayedSource() = withVirtualTime {
        val flow = flow {
            expect(1)
            delay(500)
            emit("A")
            expect(2)
        }

        val result = flow.throttleLatest(1000).toList()
        assertEquals(listOf("A"), result)
        finish(3)
    }

    @Test
    fun testCompletion() = withVirtualTime {
        val flow = flow {
            expect(1)
            emit("A")
            delay(500)
            emit("B")
            expect(2)
        }

        val result = flow.throttleLatest(1000).toList()
        assertEquals(listOf("A"), result)
        finish(3)
    }

    @Test
    fun testEmpty() = runTest {
        val flow = emptyFlow<Int>().throttleLatest(Long.MAX_VALUE)
        assertNull(flow.singleOrNull())
    }

    @Test
    fun testScalar() = withVirtualTime {
        val flow = flowOf(1, 2, 3).throttleLatest(1000)
        assertEquals(1, flow.single())
        finish(1)
    }

    @Test
    fun testUpstreamError() = testUpstreamError(TimeoutCancellationException(""))

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
        }.throttleLatest(1).map {
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
        }.flowOn(NamedDispatchers("upstream")).throttleLatest(1).map {
            latch.send(Unit)
            hang { expect(3) }
        }

        assertFailsWith<TestException>(flow)
        finish(4)
    }

    @Test
    fun testDownstreamError() = runTest {
        val flow: Flow<Int> = flow {
            expect(1)
            emit(1)
            hang { expect(3) }
        }.throttleLatest(100).map {
            expect(2)
            yield()
            throw TestException()
        }

        assertFailsWith<TestException>(flow)
        finish(4)
    }

    @Test
    fun testDownstreamErrorIsolatedContext() = runTest {
        val flow: Flow<Int> = flow {
            assertEquals("upstream", NamedDispatchers.name())
            expect(1)
            emit(1)
            hang { expect(3) }
        }.flowOn(NamedDispatchers("upstream")).throttleLatest(100).map {
            expect(2)
            yield()
            throw TestException()
        }

        assertFailsWith<TestException>(flow)
        finish(4)
    }

    @ExperimentalTime
    @Test
    fun testDurationBasic() = withVirtualTime {
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
        val result = flow.throttleLatest(1000.milliseconds).toList()
        assertEquals(listOf("A", "B", "D", "E"), result)
        finish(5)
    }
}