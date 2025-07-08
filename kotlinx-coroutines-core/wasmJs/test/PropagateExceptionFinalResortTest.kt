package kotlinx.coroutines

import kotlinx.coroutines.testing.TestBase
import kotlin.test.*

class PropagateExceptionFinalResortTest : TestBase() {
    /*
     * Test that `propagateExceptionFinalResort` re-throws the exception on Wasm/JS.
     *
     * It is checked by setting up an exception handler within Wasm/JS.
     */
    @Test
    fun testPropagateExceptionFinalResortReThrowsOnWasmJS() = runTest {
        addUncaughtExceptionHandler()
        val job = GlobalScope.launch {
            throw IllegalStateException("My ISE")
        }
        job.join()
        delay(1)  // Let the exception be re-thrown and handled.
        assertTrue(exceptionCaught())
    }
}

private fun addUncaughtExceptionHandler() {
    js("""
        globalThis.exceptionCaught = false;
        process.on('uncaughtException', function(e) {
            globalThis.exceptionCaught = true;
        });
    """)
}

private fun exceptionCaught(): Boolean = js("globalThis.exceptionCaught")
