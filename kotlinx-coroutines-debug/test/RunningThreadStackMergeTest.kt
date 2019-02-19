/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines.debug

import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import java.util.concurrent.*
import kotlin.test.*

class RunningThreadStackMergeTest : TestBase() {

    private val testMainBlocker = CountDownLatch(1) // Test body blocks on it
    private val coroutineBlocker = CyclicBarrier(2) // Launched coroutine blocks on it

    @Before
    fun setUp() {
        before()
        DebugProbes.install()
    }

    @After
    fun tearDown() {
        try {
            DebugProbes.uninstall()
        } finally {
            onCompletion()
        }
    }

    @Test
    fun testStackMergeWithContext() = runTest {
        launchCoroutine()
        awaitCoroutineStarted()

        verifyDump(
            "Coroutine \"coroutine#1\":BlockingCoroutine{Active}@62230679", // <- this one is ignored
            "Coroutine \"coroutine#2\":StandaloneCoroutine{Active}@50284dc4, state: RUNNING\n" +
                    "\tat sun.misc.Unsafe.park(Native Method)\n" +
                    "\tat java.util.concurrent.locks.LockSupport.park(LockSupport.java:175)\n" +
                    "\tat java.util.concurrent.locks.AbstractQueuedSynchronizer\$ConditionObject.await(AbstractQueuedSynchronizer.java:2039)\n" +
                    "\tat java.util.concurrent.CyclicBarrier.dowait(CyclicBarrier.java:234)\n" +
                    "\tat java.util.concurrent.CyclicBarrier.await(CyclicBarrier.java:362)\n" +
                    "\tat kotlinx.coroutines.debug.RunningThreadStackMergeTest.nonSuspendingFun(RunningThreadStackMergeTest.kt:86)\n" +
                    "\tat kotlinx.coroutines.debug.RunningThreadStackMergeTest.access\$nonSuspendingFun(RunningThreadStackMergeTest.kt:12)\n" +
                    "\tat kotlinx.coroutines.debug.RunningThreadStackMergeTest\$suspendingFunction\$2.invokeSuspend(RunningThreadStackMergeTest.kt:77)\n" +
                    "\tat kotlinx.coroutines.debug.RunningThreadStackMergeTest.suspendingFunction(RunningThreadStackMergeTest.kt:75)\n" +
                    "\tat kotlinx.coroutines.debug.RunningThreadStackMergeTest\$launchCoroutine\$1.invokeSuspend(RunningThreadStackMergeTest.kt:68)\n" +
                    "\t(Coroutine creation stacktrace)\n" +
                    "\tat kotlin.coroutines.intrinsics.IntrinsicsKt__IntrinsicsJvmKt.createCoroutineUnintercepted(IntrinsicsJvm.kt:116)",
            ignoredCoroutine = "BlockingCoroutine"
        )
        coroutineBlocker.await()
    }

    private fun awaitCoroutineStarted() {
        testMainBlocker.await()
        while (coroutineBlocker.numberWaiting != 1) {
            Thread.sleep(10)
        }
    }

    private fun CoroutineScope.launchCoroutine() {
        launch(Dispatchers.Default) {
            suspendingFunction()
            assertTrue(true)
        }
    }

    private suspend fun suspendingFunction() {
        // Typical use-case
        withContext(Dispatchers.IO) {
            yield()
            nonSuspendingFun()
        }

        assertTrue(true)
    }

    private fun nonSuspendingFun() {
        testMainBlocker.countDown()
        coroutineBlocker.await()
    }

    @Test
    fun testStackMergeEscapeSuspendMethod() = runTest {
        launchEscapingCoroutine()
        awaitCoroutineStarted()
        verifyDump(
            "Coroutine \"coroutine#1\":BlockingCoroutine{Active}@62230679", // <- this one is ignored
            "Coroutine \"coroutine#2\":StandaloneCoroutine{Active}@3aea3c67, state: RUNNING\n" +
                    "\tat sun.misc.Unsafe.park(Native Method)\n" +
                    "\tat java.util.concurrent.locks.LockSupport.park(LockSupport.java:175)\n" +
                    "\tat java.util.concurrent.locks.AbstractQueuedSynchronizer\$ConditionObject.await(AbstractQueuedSynchronizer.java:2039)\n" +
                    "\tat java.util.concurrent.CyclicBarrier.dowait(CyclicBarrier.java:234)\n" +
                    "\tat java.util.concurrent.CyclicBarrier.await(CyclicBarrier.java:362)\n" +
                    "\tat kotlinx.coroutines.debug.RunningThreadStackMergeTest.nonSuspendingFun(RunningThreadStackMergeTest.kt:83)\n" +
                    "\tat kotlinx.coroutines.debug.RunningThreadStackMergeTest.access\$nonSuspendingFun(RunningThreadStackMergeTest.kt:12)\n" +
                    "\tat kotlinx.coroutines.debug.RunningThreadStackMergeTest\$suspendingFunctionWithContext\$2.invokeSuspend(RunningThreadStackMergeTest.kt:124)\n" +
                    "\tat kotlinx.coroutines.debug.RunningThreadStackMergeTest.suspendingFunctionWithContext(RunningThreadStackMergeTest.kt:122)\n" +
                    "\tat kotlinx.coroutines.debug.RunningThreadStackMergeTest\$launchEscapingCoroutine\$1.invokeSuspend(RunningThreadStackMergeTest.kt:116)\n" +
                    "\t(Coroutine creation stacktrace)\n" +
                    "\tat kotlin.coroutines.intrinsics.IntrinsicsKt__IntrinsicsJvmKt.createCoroutineUnintercepted(IntrinsicsJvm.kt:116)",
            ignoredCoroutine = "BlockingCoroutine"
        )
        coroutineBlocker.await()
    }

    @Test
    fun testRunBlocking() = runBlocking {
        verifyDump("Coroutine \"coroutine#1\":BlockingCoroutine{Active}@4bcd176c, state: RUNNING\n" +
                "\tat java.lang.Thread.getStackTrace(Thread.java:1552)\n" +
                "\tat kotlinx.coroutines.debug.internal.DebugProbesImpl.enhanceStackTraceWithThreadDump(DebugProbesImpl.kt:147)\n" +
                "\tat kotlinx.coroutines.debug.internal.DebugProbesImpl.dumpCoroutines(DebugProbesImpl.kt:122)\n" +
                "\tat kotlinx.coroutines.debug.internal.DebugProbesImpl.dumpCoroutines(DebugProbesImpl.kt:109)\n" +
                "\tat kotlinx.coroutines.debug.DebugProbes.dumpCoroutines(DebugProbes.kt:122)\n" +
                "\tat kotlinx.coroutines.debug.StracktraceUtilsKt.verifyDump(StracktraceUtils.kt)\n" +
                "\tat kotlinx.coroutines.debug.StracktraceUtilsKt.verifyDump\$default(StracktraceUtils.kt)\n" +
                "\tat kotlinx.coroutines.debug.RunningThreadStackMergeTest\$testRunBlocking\$1.invokeSuspend(RunningThreadStackMergeTest.kt:112)\n" +
                "\t(Coroutine creation stacktrace)\n" +
                "\tat kotlin.coroutines.intrinsics.IntrinsicsKt__IntrinsicsJvmKt.createCoroutineUnintercepted(IntrinsicsJvm.kt:116)\n")
    }

    private fun CoroutineScope.launchEscapingCoroutine() {
        launch(Dispatchers.Default) {
            suspendingFunctionWithContext()
            assertTrue(true)
        }
    }

    private suspend fun suspendingFunctionWithContext() {
        withContext(Dispatchers.IO) {
            actualSuspensionPoint()
            nonSuspendingFun()
        }

        assertTrue(true)
    }

    private suspend fun actualSuspensionPoint() {
        nestedSuspensionPoint()
        assertTrue(true)
    }

    private suspend fun nestedSuspensionPoint() {
        yield()
        assertTrue(true)
    }
}
