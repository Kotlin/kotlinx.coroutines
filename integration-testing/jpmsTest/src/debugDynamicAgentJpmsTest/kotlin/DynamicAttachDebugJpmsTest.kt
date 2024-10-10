@file:OptIn(ExperimentalCoroutinesApi::class)

import org.junit.*
import kotlinx.coroutines.*
import kotlinx.coroutines.debug.*
import org.junit.Ignore
import org.junit.Test
import java.io.*
import java.lang.IllegalStateException
import kotlin.test.*

class DynamicAttachDebugJpmsTest {

    /**
     * This test is disabled because:
     * Dynamic Attach with JPMS is not yet supported.
     *
     * Here is the state of experiments:
     * When launching this test with additional workarounds like
     * ```
     *     jvmArgs("--add-exports=kotlinx.coroutines.debug/kotlinx.coroutines.repackaged.net.bytebuddy=com.sun.jna")
     *     jvmArgs("--add-exports=kotlinx.coroutines.debug/kotlinx.coroutines.repackaged.net.bytebuddy.agent=com.sun.jna")
     *```
     *
     * Then we see issues like
     *
     * ```
     * Caused by: java.lang.IllegalStateException: The Byte Buddy agent is not loaded or this method is not called via the system class loader
     * 	at kotlinx.coroutines.debug/kotlinx.coroutines.repackaged.net.bytebuddy.agent.Installer.getInstrumentation(Installer.java:61)
     * 	... 54 more
     * 	```
     */
    @Ignore("shaded byte-buddy does not work with JPMS")
    @Test
    fun testAgentDumpsCoroutines() =
        DebugProbes.withDebugProbes {
            runBlocking {
                val baos = ByteArrayOutputStream()
                DebugProbes.dumpCoroutines(PrintStream(baos))
                // if the agent works, then dumps should contain something,
                // at least the fact that this test is running.
                Assert.assertTrue(baos.toString().contains("testAgentDumpsCoroutines"))
            }
        }

    @Test
    fun testAgentIsNotInstalled() {
        assertEquals(false, DebugProbes.isInstalled)
        assertFailsWith<IllegalStateException> {
            DebugProbes.dumpCoroutines(PrintStream(ByteArrayOutputStream()))
        }
    }

}
