/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.operators

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.test.*
import kotlin.time.Duration.Companion.milliseconds

class TimeoutTest : TestBase() {
    @Test
    fun testBasic() = withVirtualTime {
        expect(1)
        val flow = flow {
            expect(3)
            emit("A")
            delay(100)
            emit("B")
            delay(100)
            emit("C")
            expect(4)
            delay(400)
            expectUnreached()
        }

        expect(2)
        val list = mutableListOf<String>()
        assertFailsWith<TimeoutCancellationException>(flow.timeout(300.milliseconds).onEach { list.add(it) })
        assertEquals(listOf("A", "B", "C"), list)
        finish(5)
    }

    @Test
    fun testSingleNull() = withVirtualTime {
        val flow = flow<Int?> {
            emit(null)
            delay(1)
            expect(1)
        }.timeout(2.milliseconds)
        assertNull(flow.single())
        finish(2)
    }

    @Test
    fun testBasicCustomAction() = withVirtualTime {
        expect(1)
        val flow = flow {
            expect(3)
            emit("A")
            delay(100)
            emit("B")
            delay(100)
            emit("C")
            expect(4)
            delay(400)
            expectUnreached()
        }

        expect(2)
        val list = mutableListOf<String>()
        flow.timeout(300.milliseconds).catch { if (it is TimeoutCancellationException) emit("-1") }.collect { list.add(it) }
        assertEquals(listOf("A", "B", "C", "-1"), list)
        finish(5)
    }

    @Test
    fun testDelayedFirst() = withVirtualTime {
        expect(1)
        val flow = flow {
            expect(3)
            delay(100)
            emit(1)
            expect(4)
        }.timeout(250.milliseconds)
        expect(2)
        assertEquals(1, flow.singleOrNull())
        finish(5)
    }

    @Test
    fun testEmpty() = withVirtualTime {
        val flow = emptyFlow<Any?>().timeout(1.milliseconds)
        assertNull(flow.singleOrNull())
        finish(1)
    }

    @Test
    fun testScalar() = withVirtualTime {
        val flow = flowOf(1, 2, 3).timeout(1.milliseconds)
        assertEquals(listOf(1, 2, 3), flow.toList())
        finish(1)
    }

    @Test
    fun testUpstreamError() = testUpstreamError(TestException())

    @Test
    fun testUpstreamErrorTimeoutException() = testUpstreamError(TimeoutCancellationException(0, Job()))

    private inline fun <reified T: Throwable> testUpstreamError(cause: T) = runTest {
        try {
            // Workaround for JS legacy bug
            flow {
                emit(1)
                throw cause
            }.timeout(1.milliseconds).collect()
            expectUnreached()
        } catch (e: Throwable) {
            assertTrue { e is T }
            finish(1)
        }
    }

    @Test
    fun testDownstreamError() = runTest {
        val flow = flow {
            expect(1)
            emit(1)
            hang { expect(3) }
            expectUnreached()
        }.timeout(100.milliseconds).map {
            expect(2)
            yield()
            throw TestException()
        }

        assertFailsWith<TestException>(flow)
        finish(4)
    }

    @Test
    fun testUpstreamTimeoutIsolatedContext() = runTest {
        val flow = flow {
            assertEquals("upstream", NamedDispatchers.name())
            expect(1)
            emit(1)
            expect(2)
            delay(300)
            expectUnreached()
        }.flowOn(NamedDispatchers("upstream")).timeout(100.milliseconds)

        assertFailsWith<TimeoutCancellationException>(flow)
        finish(3)
    }

    @Test
    fun testUpstreamTimeoutActionIsolatedContext() = runTest {
        val flow = flow {
            assertEquals("upstream", NamedDispatchers.name())
            expect(1)
            emit(1)
            expect(2)
            delay(300)
            expectUnreached()
        }.flowOn(NamedDispatchers("upstream")).timeout(100.milliseconds).catch {
            expect(3)
            emit(2)
        }

        assertEquals(listOf(1, 2), flow.toList())
        finish(4)
    }

    @Test
    fun testUpstreamNoTimeoutIsolatedContext() = runTest {
        val flow = flow {
            assertEquals("upstream", NamedDispatchers.name())
            expect(1)
            emit(1)
            expect(2)
            delay(10)
        }.flowOn(NamedDispatchers("upstream")).timeout(100.milliseconds)

        assertEquals(listOf(1), flow.toList())
        finish(3)
    }

    @Test
    fun testSharedFlowTimeout() = runTest {
        // Workaround for JS legacy bug
        try {
            MutableSharedFlow<Int>().asSharedFlow().timeout(100.milliseconds).collect()
            expectUnreached()
        } catch (e: TimeoutCancellationException) {
            finish(1)
        }
    }

    @Test
    fun testSharedFlowCancelledNoTimeout() = runTest {
        val mutableSharedFlow = MutableSharedFlow<Int>()
        val list = arrayListOf<Int>()

        expect(1)
        val consumerJob = launch {
            expect(3)
            mutableSharedFlow.asSharedFlow().timeout(100.milliseconds).collect { list.add(it) }
            expectUnreached()
        }
        val producerJob = launch {
            expect(4)
            repeat(10) {
                delay(50)
                mutableSharedFlow.emit(it)
            }
            yield()
            consumerJob.cancel()
            expect(5)
        }

        expect(2)

        producerJob.join()
        consumerJob.join()

        assertEquals((0 until 10).toList(), list)
        finish(6)
    }
}
