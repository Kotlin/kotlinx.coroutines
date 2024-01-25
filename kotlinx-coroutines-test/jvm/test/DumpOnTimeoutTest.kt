package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.debug.*
import org.junit.Test
import java.io.*
import kotlin.test.*
import kotlin.time.Duration.Companion.milliseconds

class DumpOnTimeoutTest {
    /**
     * Tests that the dump on timeout contains the correct stacktrace.
     */
    @Test
    fun testDumpOnTimeout() {
        val oldErr = System.err
        val baos = ByteArrayOutputStream()
        try {
            System.setErr(PrintStream(baos, true))
            DebugProbes.withDebugProbes {
                try {
                    runTest(timeout = 100.milliseconds) {
                        uniquelyNamedFunction()
                    }
                    throw IllegalStateException("unreachable")
                } catch (e: UncompletedCoroutinesError) {
                    // do nothing
                }
            }
            baos.toString().let {
                assertTrue(it.contains("uniquelyNamedFunction"), "Actual trace:\n$it")
            }
        } finally {
            System.setErr(oldErr)
        }
    }

    fun CoroutineScope.uniquelyNamedFunction() {
        while (true) {
            ensureActive()
            Thread.sleep(10)
        }
    }
}
