import org.junit.*
import kotlinx.coroutines.*
import kotlinx.coroutines.debug.internal.*
import org.junit.Test
import java.io.*

class CoreAgentTest {

    @Test
    fun testAgentDumpsCoroutines() = runBlocking {
        val baos = ByteArrayOutputStream()
        @Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE")
        DebugProbesImpl.dumpCoroutines(PrintStream(baos))
        // if the agent works, then dumps should contain something,
        // at least the fact that this test is running.
        Assert.assertTrue(baos.toString().contains("testAgentDumpsCoroutines"))
    }

}
