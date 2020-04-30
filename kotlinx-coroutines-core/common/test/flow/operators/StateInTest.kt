package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class StateInTest : TestBase() {
    @Test
    fun testEmptyFlow() = runTest {
        assertFailsWith<NoSuchElementException> {
            emptyFlow<Int>().stateIn(this)
        }
    }

    @Test
    fun testEmptyFlowNullValue() = runTest {
        val state = emptyFlow<Int>().stateIn(this, null)
        assertEquals(null, state.value)
        assertFalse(state.isClosed)
        yield()
        assertEquals(null, state.value)
        assertTrue(state.isClosed)
    }

    @Test
    fun testEmptyFlowZeroValue() = runTest {
        val state = emptyFlow<Int>().stateIn(this, 0)
        assertEquals(0, state.value)
        assertFalse(state.isClosed)
        yield()
        assertEquals(0, state.value)
        assertTrue(state.isClosed)
    }

    @Test
    fun testFailingFlow() = runTest {
        assertFailsWith<TestException> {
            flow<Int> { throw TestException() }.stateIn(this)
        }
    }

    @Test
    fun testFailingFlowValue() = runTest {
        expect(1)
        val state = flow<Int> { throw TestException() }.stateIn(this, 42)
        assertEquals(42, state.value)
        assertFalse(state.isClosed)
        yield()
        assertEquals(42, state.value)
        assertTrue(state.isClosed)
        assertFailsWith<TestException> {
            expect(2)
            state.collect { value ->
                assertEquals(42, value)
                expect(3)
            }
        }
        finish(4)
    }

    @Test
    fun testOneElementFlow() = runTest {
        val state = flowOf("OK").onCompletion { yield() }.stateIn(this)
        assertEquals("OK", state.value)
        assertFalse(state.isClosed)
        yield()
        assertEquals("OK", state.value)
        assertTrue(state.isClosed)
    }

    @Test
    fun testOneElementFlowValue() = runTest {
        val state = flowOf("OK").stateIn(this, "INIT")
        assertEquals("INIT", state.value)
        assertFalse(state.isClosed)
        yield()
        assertEquals("OK", state.value)
        assertTrue(state.isClosed)
    }

    @Test
    fun testStateFlowJobCancellation() = runTest {
        val flow = flow<Int> {
            repeat(10) {
                emit(it)
                yield()
            }
        }
        val state = flow.stateIn(this)
        assertEquals(0, state.value)
        yield()
        assertEquals(1, state.value)
        state.cancel() // cancel this job
        yield()
        assertEquals(1, state.value)
        assertTrue(state.isClosed)
        // check that state is closed normally with value one
        assertEquals(listOf(1), state.toList())
    }

    @Test
    fun testStateFlowFailure() = runTest {
        expect(1)
        val flow = flow<String> {
            expect(2)
            emit("OK")
            yield()
            expect(4)
            throw TestException()
        }
        val state = flow.stateIn(this)
        expect(3)
        assertEquals("OK", state.value)
        assertFalse(state.isClosed)
        yield()
        expect(5)
        assertEquals("OK", state.value)
        assertTrue(state.isClosed)
        // try to collect fails after producing the value
        assertFailsWith<TestException> {
            expect(6)
            state.collect {
                assertEquals("OK", it)
                expect(7)
            }
        }
        finish(8)
    }
}