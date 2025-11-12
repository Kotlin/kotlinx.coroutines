package kotlinx.coroutines

import kotlinx.coroutines.testing.TestBase
import kotlin.test.*

class PropagateExceptionFinalResortTest : TestBase() {
    @BeforeTest
    private fun addUncaughtExceptionHandler() {
        addUncaughtExceptionHandlerHelper()
    }

    @AfterTest
    private fun removeHandler() {
        removeHandlerHelper()
    }

    /*
     * Test that `propagateExceptionFinalResort` re-throws the exception on Wasm/JS.
     *
     * It is checked by setting up an exception handler within Wasm/JS.
     */
    @Test
    fun testPropagateExceptionFinalResortReThrowsOnWasmJS() = runTest {
        val job = GlobalScope.launch {
            throw IllegalStateException("My ISE")
        }
        job.join()
        delay(1) // Let the exception be re-thrown and handled.
        assertTrue(exceptionCaught())
    }
}

@OptIn(ExperimentalWasmJsInterop::class)
private fun addUncaughtExceptionHandlerHelper() {
    js("""
            globalThis.exceptionCaught = false;
            globalThis.exceptionHandler = function(e) {
                globalThis.exceptionCaught = true;
            };
            process.on('uncaughtException', globalThis.exceptionHandler);
        """)
}

@OptIn(ExperimentalWasmJsInterop::class)
private fun removeHandlerHelper() {
    js("""
            process.removeListener('uncaughtException', globalThis.exceptionHandler);
        """)
}

@OptIn(ExperimentalWasmJsInterop::class)
private fun exceptionCaught(): Boolean = js("globalThis.exceptionCaught")
