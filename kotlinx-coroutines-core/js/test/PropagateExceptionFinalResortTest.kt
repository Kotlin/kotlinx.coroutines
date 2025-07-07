package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.js.*
import kotlin.test.*

class PropagateExceptionFinalResortTest : TestBase() {
    @BeforeTest
    fun setupExceptionListenerOnly() {
        // Remove a Node.js's internal listener, which prints the exception to stdout.
        js("""
            globalThis.originalListeners = process.listeners('uncaughtException');
            process.removeAllListeners('uncaughtException');
        """)
    }

    @AfterTest
    fun restoreListeners() {
        js("""
            if (globalThis.originalListeners) {
                process.removeAllListeners('uncaughtException');
                globalThis.originalListeners.forEach(function(listener) {
                    process.on('uncaughtException', listener);
                });
            }
        """)
    }

    @Test
    fun testThrows() = runTest {
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
        delay(1)
        val exceptionCaught = js("globalThis.exceptionCaught") as Boolean
        assertTrue(exceptionCaught)
    }
}
