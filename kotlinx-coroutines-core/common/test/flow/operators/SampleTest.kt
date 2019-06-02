/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.operators

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import kotlin.test.*

class SampleTest : TestBase() {
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
        val result = flow.sample(1000).toList()
        assertEquals(listOf("A", "B", "D"), result)
        finish(5)
    }

    @Test
    fun testDelayedFirst() = withVirtualTime {
        val flow = flow {
            delay(60)
            emit(1)
            delay(60)
            expect(1)
        }.sample(100)
        assertEquals(1, flow.singleOrNull())
        finish(2)
    }

    @Test
    fun testBasic2() = withVirtualTime {
        expect(1)
        val flow = flow {
            expect(3)
            emit(1)
            emit(2)
            delay(501)
            emit(3)
            delay(100)
            emit(4)
            delay(100)
            emit(5)
            emit(6)
            delay(301)
            emit(7)
            delay(501)
            expect(4)
        }

        expect(2)
        val result = flow.sample(500).toList()
        assertEquals(listOf(2, 6, 7), result)
        finish(5)
    }

    @Test
    fun testFixedDelay() = withVirtualTime {
        val flow = flow {
            emit("A")
            delay(150)
            emit("B")
            expect(1)
        }.sample(100)
        assertEquals("A", flow.single())
        finish(2)
    }

    @Test
    fun testSingleNull() = withVirtualTime {
        val flow = flow<Int?> {
            emit(null)
            delay(2)
            expect(1)
        }.sample(1)
        assertNull(flow.single())
        finish(2)
    }

    @Test
    fun testBasicWithNulls() = withVirtualTime {
        expect(1)
        val flow = flow {
            expect(3)
            emit("A")
            delay(1500)
            emit(null)
            delay(500)
            emit("C")
            delay(250)
            emit(null)
            delay(2000)
            emit("E")
            expect(4)
        }

        expect(2)
        val result = flow.sample(1000).toList()
        assertEquals(listOf("A", null, null), result)
        finish(5)
    }

    @Test
    fun testEmpty() = runTest {
        val flow = emptyFlow<Int>().sample(Long.MAX_VALUE)
        assertNull(flow.singleOrNull())
    }

    @Test
    fun testScalar() = runTest {
        val flow = flowOf(1, 2, 3).sample(Long.MAX_VALUE)
        assertNull(flow.singleOrNull())
    }

    @Test
    // note that this test depends on the sampling strategy -- when sampling time starts on a quiescent flow that suddenly emits
    fun testLongWait() = withVirtualTime {
        expect(1)
        val flow = flow {
            expect(2)
            emit("A")
            delay(3500) // long delay -- multiple sampling intervals
            emit("B")
            delay(900) // crosses time = 4000 barrier
            emit("C")
            delay(3000) // long wait again

        }
        val result = flow.sample(1000).toList()
        assertEquals(listOf("A", "B", "C"), result)
        finish(3)
    }

    @Test
    fun testPace() = withVirtualTime {
        val flow = flow {
            expect(1)
            repeat(4) {
                emit(-it)
                delay(50)
            }

            repeat(4) {
                emit(it)
                delay(100)
            }
            expect(2)
        }.sample(100)

        assertEquals(listOf(-1, -3, 0, 1, 2, 3), flow.toList())
        finish(3)
    }

    @Test
    fun testUpstreamError() = runTest {
        val latch = Channel<Unit>()
        val flow = flow {
            expect(1)
            emit(1)
            expect(2)
            latch.receive()
            throw TestException()
        }.sample(1).map {
            latch.send(Unit)
            hang { expect(3) }
        }

        assertFailsWith<TestException>(flow)
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
        }.flowOn(NamedDispatchers("upstream")).sample(1).map {
            latch.send(Unit)
            hang { expect(3) }
        }

        assertFailsWith<TestException>(flow)
        finish(4)
    }

    @Test
    fun testUpstreamErrorSampleNotTriggered() = runTest {
        val flow = flow {
            expect(1)
            emit(1)
            expect(2)
            throw TestException()
        }.sample(Long.MAX_VALUE).map {
            expectUnreached()
        }
        assertFailsWith<TestException>(flow)
        finish(3)
    }


    @Test
    fun testUpstreamErrorSampleNotTriggeredInIsolatedContext() = runTest {
        val flow = flow {
            expect(1)
            emit(1)
            expect(2)
            throw TestException()
        }.flowOn(NamedDispatchers("unused")).sample(Long.MAX_VALUE).map {
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
        }.sample(100).map {
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
        }.flowOn(NamedDispatchers("upstream")).sample(100).map {
            expect(2)
            yield()
            throw TestException()
            it
        }

        assertFailsWith<TestException>(flow)
        finish(4)
    }
}
