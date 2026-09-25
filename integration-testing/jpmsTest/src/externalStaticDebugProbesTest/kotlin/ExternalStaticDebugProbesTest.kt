import org.junit.*
import kotlinx.coroutines.*
import kotlinx.coroutines.external.ExternalStaticDebugProbes
import org.junit.Test
import java.io.*

class ExternalStaticDebugProbesTest {

    @Test
    fun testDumpCoroutines() {
        runBlocking {
            val baos = ByteArrayOutputStream()
            ExternalStaticDebugProbes.dumpCoroutines(PrintStream(baos))
            // if the agent works, then dumps should contain something,
            // at least the fact that this test is running.
            val dump = baos.toString()
            Assert.assertTrue(dump, dump.contains("testDumpCoroutines"))
        }
    }
}
