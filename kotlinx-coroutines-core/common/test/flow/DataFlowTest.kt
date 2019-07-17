/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class DataFlowTest : TestBase() {
    @Test
    fun testUninitializedAndNormalClose() = runTest {
        expect(1)
        val data = DataFlow<Int?>()
        assertFalse(data.isInitialized)
        assertFalse(data.isClosed)
        assertFailsWith<IllegalStateException> { data.value }
        launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            data.collect { value ->
                when (value) {
                    1 -> expect(4)
                    null -> expect(7)
                    2 -> expect(9)
                    else -> expectUnreached()
                }
            }
            expect(11)
        }
        expect(3) // collector is waiting
        data.value = 1 // fire in the hole!
        assertTrue(data.isInitialized)
        assertFalse(data.isClosed)
        assertEquals(1, data.value)
        yield()
        expect(5)
        data.value = 1 // same value, nothing happens
        yield()
        expect(6)
        data.value = null // null value
        assertTrue(data.isInitialized)
        assertFalse(data.isClosed)
        assertNull(data.value)
        yield()
        expect(8)
        data.value = 2 // another value
        assertTrue(data.isInitialized)
        assertFalse(data.isClosed)
        assertEquals(2, data.value)
        yield()
        expect(10)
        data.close()
        assertTrue(data.isInitialized)
        assertTrue(data.isClosed)
        assertFailsWith<IllegalStateException> { data.value }
        yield()
        finish(12)
    }

    @Test
    fun testInitializedAndCloseWithException() = runTest {
        expect(1)
        val data = DataFlow("A")
        assertTrue(data.isInitialized)
        assertFalse(data.isClosed)
        assertEquals("A", data.value)
        launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            try {
                data.collect { value ->
                    when (value) {
                        "A" -> expect(3)
                        "B" -> expect(5)
                        else -> expectUnreached()
                    }
                }
            } catch (e: TestException) {
                expect(7)
                return@launch
            }
            expectUnreached()
        }
        expect(4)
        data.value = "B"
        assertTrue(data.isInitialized)
        assertFalse(data.isClosed)
        assertEquals("B", data.value)
        yield()
        expect(6)
        data.close(TestException("OK"))
        assertTrue(data.isInitialized)
        assertTrue(data.isClosed)
        assertFailsWith<IllegalStateException> { data.value }
        yield()
        finish(8)
    }

    @Test
    fun testDataModel() = runTest {
        val s = CounterModel()
        launch {
            val sum = s.counter.take(11).sum()
            assertEquals(55, sum)
        }
        repeat(10) {
            yield()
            s.inc()
        }
    }

    class CounterModel {
        // private data flow
        private val _counter = DataFlow(0)
        // publicly exposed as a flow
        val counter: Flow<Int> get() = _counter

        fun inc() {
            _counter.value++
        }
    }
}