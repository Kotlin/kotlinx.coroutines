package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.js.*
import kotlin.test.*

class PropagateExceptionFinalResortTest : TestBase() {
    @BeforeTest
    private fun removeListeners() {
        // Remove a Node.js's internal listener, which prints the exception to stdout.
        js("""
            globalThis.originalListeners = process.listeners('uncaughtException');
            process.removeAllListeners('uncaughtException');
        """)
    }

    @AfterTest
    private fun restoreListeners() {
        js("""
            if (globalThis.originalListeners) {
                process.removeAllListeners('uncaughtException');
                globalThis.originalListeners.forEach(function(listener) {
                    process.on('uncaughtException', listener);
                });
            }
        """)
    }

    /*
     * Test that `propagateExceptionFinalResort` re-throws the exception on JS.
     *
     * It is checked by setting up an exception handler within JS.
     */
    @Test
    fun testPropagateExceptionFinalResortReThrowsOnNodeJS() = runTest {
        js("""
            globalThis.exceptionCaught = false;
            process.on('uncaughtException', function(e) {
                globalThis.exceptionCaught = true;
            });
        """)
        val job = GlobalScope.launch {
            throw IllegalStateException("My ISE")
        }
        job.join()
        delay(1) // Let the exception be re-thrown and handled.
        val exceptionCaught = js("globalThis.exceptionCaught") as Boolean
        assertTrue(exceptionCaught)
    }
}
