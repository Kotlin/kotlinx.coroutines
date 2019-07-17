/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class StateFlowTest : TestBase() {
    @Test
    fun testUninitializedAndNormalClose() = runTest {
        expect(1)
        val state = StateFlow<Int?>()
        assertFalse(state.isInitialized)
        assertFalse(state.isClosed)
        assertFailsWith<IllegalStateException> { state.value }
        launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            state.collect { value ->
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
        state.value = 1 // fire in the hole!
        assertTrue(state.isInitialized)
        assertFalse(state.isClosed)
        assertEquals(1, state.value)
        yield()
        expect(5)
        state.value = 1 // same value, nothing happens
        yield()
        expect(6)
        state.value = null // null value
        assertTrue(state.isInitialized)
        assertFalse(state.isClosed)
        assertNull(state.value)
        yield()
        expect(8)
        state.value = 2 // another value
        assertTrue(state.isInitialized)
        assertFalse(state.isClosed)
        assertEquals(2, state.value)
        yield()
        expect(10)
        state.close()
        assertTrue(state.isInitialized)
        assertTrue(state.isClosed)
        assertFailsWith<IllegalStateException> { state.value }
        yield()
        finish(12)
    }

    @Test
    fun testInitializedAndCloseWithException() = runTest {
        expect(1)
        val state = StateFlow("A")
        assertTrue(state.isInitialized)
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
        assertTrue(state.isInitialized)
        assertFalse(state.isClosed)
        assertEquals("B", state.value)
        yield()
        expect(6)
        state.close(TestException("OK"))
        assertTrue(state.isInitialized)
        assertTrue(state.isClosed)
        assertFailsWith<IllegalStateException> { state.value }
        yield()
        finish(8)
    }

    @Test
    fun testDataModel() = runTest {
        val model = CounterModel()
        launch {
            val sum = model.flow.take(11).sum()
            assertEquals(55, sum)
        }
        repeat(10) {
            yield()
            model.inc()
        }
    }

    class CounterModel {
        private val _flow = StateFlow(0) // private mutable state flow
        val flow: StateFlow<Int> get() = _flow // publicly exposed as a state flow
        var value: Int by _flow // publicly exposed value
            private set // setting only privately

        fun inc() { value++ }
    }

    // tests creation/freeing of many collectors
    @Test
    fun testCollectorsCreateFreeChurn() = runTest  {
        expect(1)
        val nCol = 100 // initial number of collectors
        val state = StateFlow<String>()
        // launch nCol collectors
        var cReceived = 0
        repeat(nCol) { index ->
            launch(start = CoroutineStart.UNDISPATCHED) {
                state.collect { value ->
                    when (value) {
                        "A" -> {
                            expect(index + 2)
                            // odd collectors die
                            if (index % 2 != 0) throw CancellationException("Die")
                        }
                        "B" -> {
                            expect(nCol + 3 + index / 2)
                            // only even collectors can receive it
                            assertTrue(index % 2 == 0)
                        }
                        "C" -> { // order of reception is going to be impl-dependent, just count # of receives here
                            cReceived++
                        }
                        else -> error("Unexpected $value")
                    }
                }
            }
        }
        // update value to "A"
        state.value = "A"
        yield() // to collectors, they receive values in order of their creation, odd collectors die
        expect(nCol + 2)
        state.value = "B"
        yield() // to collectors, remaining even collectors receive it
        expect(3 * nCol / 2 + 3)
        // launch nCol more collectors (reusing half of the indices and allocating more)
        repeat(nCol) { index ->
            launch(start = CoroutineStart.UNDISPATCHED) {
                state.collect { value ->
                    when (value) {
                        "B" -> {
                            // initial value on their creating immediately processed
                            expect(3 * nCol / 2 + 4 + index)
                        }
                        "C" -> { // order of reception is going to be impl-dependent, just count # of receives here
                            cReceived++
                        }
                        else -> error("Unexpected $value")
                    }
                }
            }
        }
        // sends new value to all 3 * nCol / 2 active collectors
        state.value = "C"
        yield() // to all collectors
        assertEquals(3 * nCol / 2, cReceived)
        // close state
        state.close()
        // done
        finish(5 * nCol / 2 + 4)
    }
}