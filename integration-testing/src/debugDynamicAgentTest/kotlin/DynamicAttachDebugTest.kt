/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
import org.junit.*
import kotlinx.coroutines.*
import kotlinx.coroutines.debug.*
import org.junit.Test
import java.io.*
import java.lang.IllegalStateException

class DynamicAttachDebugTest {

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

    @Test(expected = IllegalStateException::class)
    fun testAgentIsNotInstalled() {
        DebugProbes.dumpCoroutines(PrintStream(ByteArrayOutputStream()))
    }
}
