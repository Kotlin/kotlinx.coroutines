package kotlinx.coroutines

import kotlinx.coroutines.testing.TestBase
import kotlin.test.*

fun addUncaughtExceptionHandler() {
    js("""
        globalThis.exceptionCaught = false;
        process.on('uncaughtException', function(e) {
            globalThis.exceptionCaught = true;
        });
    """)
}

fun exceptionCaught(): Boolean = js("globalThis.exceptionCaught")

class PropagateExceptionFinalResortTest : TestBase() {
    @Test
    fun testThrows() = runTest {
        addUncaughtExceptionHandler()
        val job = GlobalScope.launch {
            throw IllegalStateException("My ISE")
        }
        job.join()
        delay(1)
        assertTrue(exceptionCaught())
    }
}
