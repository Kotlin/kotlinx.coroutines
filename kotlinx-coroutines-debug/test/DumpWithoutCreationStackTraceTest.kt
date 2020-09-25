/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines.debug

import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import kotlin.test.*

class DumpWithoutCreationStackTraceTest : DebugTestBase() {
    @Before
    override fun setUp() {
        super.setUp()
        DebugProbes.enableCreationStackTraces = false
    }

    @Test
    fun testCoroutinesDump() = runTest {
        val deferred = createActiveDeferred()
        yield()
        verifyDump(
            "Coroutine \"coroutine#1\":BlockingCoroutine{Active}@70d1cb56, state: RUNNING\n" +
                    "\tat java.lang.Thread.getStackTrace(Thread.java)\n" +
                    "\tat kotlinx.coroutines.debug.internal.DebugProbesImpl.enhanceStackTraceWithThreadDumpImpl(DebugProbesImpl.kt)\n" +
                    "\tat kotlinx.coroutines.debug.internal.DebugProbesImpl.dumpCoroutinesSynchronized(DebugProbesImpl.kt)\n" +
                    "\tat kotlinx.coroutines.debug.internal.DebugProbesImpl.dumpCoroutines(DebugProbesImpl.kt)",

            "Coroutine \"coroutine#2\":DeferredCoroutine{Active}@383fa309, state: SUSPENDED\n" +
                    "\tat kotlinx.coroutines.debug.DumpWithoutCreationStackTraceTest\$createActiveDeferred\$1.invokeSuspend(DumpWithoutCreationStackTraceTest.kt)"
        )
        deferred.cancelAndJoin()
    }


    private fun CoroutineScope.createActiveDeferred(): Deferred<*> = async {
        suspendingMethod()
        assertTrue(true)
    }

    private suspend fun suspendingMethod() {
        delay(Long.MAX_VALUE)
    }
}
