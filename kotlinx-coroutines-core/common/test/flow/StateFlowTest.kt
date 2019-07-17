/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class StateFlowTest : TestBase() {
    @Test
    fun testNullAndNormalClose() = runTest {
        expect(1)
        val state = StateFlow<Int?>(0)
        assertFalse(state.isClosed)
        launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            state.collect { value ->
                when (value) {
                    0 -> expect(3)
                    1 -> expect(5)
                    null -> expect(8)
                    2 -> expect(10)
                    else -> expectUnreached()
                }
            }
            expect(12)
        }
        expect(4) // collector is waiting
        state.value = 1 // fire in the hole!
        assertFalse(state.isClosed)
        assertEquals(1, state.value)
        yield()
        expect(6)
        state.value = 1 // same value, nothing happens
        yield()
        expect(7)
        state.value = null // null value
        assertFalse(state.isClosed)
        assertNull(state.value)
        yield()
        expect(9)
        state.value = 2 // another value
        assertFalse(state.isClosed)
        assertEquals(2, state.value)
        yield()
        expect(11)
        state.close()
        assertTrue(state.isClosed)
        assertEquals(2, state.value) // the last value is still there
        yield()
        finish(13)
    }

    @Test
    fun testCloseWithException() = runTest {
        expect(1)
        val state = StateFlow("A")
        assertFalse(state.isClosed)
        assertEquals("A", state.value)
        launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            try {
                state.collect { value ->
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
        state.value = "B"
        assertFalse(state.isClosed)
        assertEquals("B", state.value)
        yield()
        expect(6)
        state.close(TestException("OK"))
        assertTrue(state.isClosed)
        assertEquals("B", state.value) // the last value is still there
        yield()
        finish(8)
    }

    @Test
    fun testCollectClosed() = runTest {
        expect(1)
        val state = StateFlow(0)
        launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            assertEquals(listOf(0, 42), state.toList()) // collects initial value and update
            expect(3)
        }
        state.value = 42 // update
        state.close() // and immediately close
        yield()
        assertEquals(listOf(42), state.toList()) // last value only when collecting from closed state flow
        finish(4)
    }

    @Test
    fun testEqualsConflation() = runTest {
        expect(1)
        val state = StateFlow(Data(0))
        launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            state.collect { value ->
                when(value.i) {
                    0 -> expect(3) // initial value
                    2 -> expect(5)
                    4 -> expect(7)
                    else -> error("Unexpected $value")
                }
            }
            expect(9)
        }
        state.value = Data(1) // conflated
        state.value = Data(0) // equals to last emitted
        yield() // no repeat zero
        state.value = Data(3) // conflated
        state.value = Data(2) // delivered
        expect(4)
        yield()
        state.value = Data(2) // equals to last one, dropped
        yield()
        state.value = Data(5) // conflated
        state.value = Data(4) // delivered
        expect(6)
        yield()
        state.close() // last value will not repeat as a side-effect of close!
        expect(8)
        yield()
        finish(10)
    }

    data class Data(val i: Int)

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
        private val _counter = StateFlow(0)
        // publicly exposed as a flow
        val counter: StateFlow<Int> get() = _counter

        fun inc() {
            _counter.value++
        }
    }
}