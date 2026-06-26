package kotlinx.coroutines

import kotlinx.coroutines.testing.TestBase
import kotlin.test.*

class MissingMainDispatcherTest : TestBase() {

    /**
     * Tests that a missing [Dispatchers.Main] throws an exception.
     *
     * In `kotlinx-coroutines-core`, there is no [Dispatchers.Main] dispatcher by default.
     */
    @Test
    fun testMissingMainDispatcher() {
        assertFailsWith<IllegalStateException> { Dispatchers.Main }
    }

    /**
     * Tests that several independent exceptions are created with relevant stack traces
     * for different [Dispatchers.Main] calls.
     */
    @Test
    fun testMissingMainDispatcherExceptionStackTrace() {
        val fooException = assertFailsWith<IllegalStateException> { foo() }
        val barException = assertFailsWith<IllegalStateException> { bar() }
        fooException.stackTraceToString().let {
            assertTrue(it.contains("foo"))
            assertFalse(it.contains("bar"))
        }
        barException.stackTraceToString().let {
            assertFalse(it.contains("foo"))
            assertTrue(it.contains("bar"))
        }
    }

    private fun foo() {
        Dispatchers.Main
    }

    private fun bar() {
        Dispatchers.Main
    }
}
