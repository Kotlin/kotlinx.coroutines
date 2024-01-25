import org.junit.*
import kotlinx.coroutines.*
import kotlinx.coroutines.debug.*
import org.junit.Test
import java.io.*

class DebugAgentTest {

    @Test
    fun testAgentDumpsCoroutines() = runBlocking {
        val baos = ByteArrayOutputStream()
        DebugProbes.dumpCoroutines(PrintStream(baos))
        // if the agent works, then dumps should contain something,
        // at least the fact that this test is running.
        Assert.assertTrue(baos.toString().contains("testAgentDumpsCoroutines"))
    }

}
