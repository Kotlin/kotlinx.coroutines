/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE")
package kotlinx.coroutines.debug

import kotlinx.coroutines.*
import kotlinx.coroutines.debug.internal.*
import org.junit.Test
import java.util.concurrent.*
import kotlin.test.*

class RunningThreadStackMergeTest : DebugTestBase() {

    private val testMainBlocker = CountDownLatch(1) // Test body blocks on it
    private val coroutineBlocker = CyclicBarrier(2) // Launched coroutine blocks on it

    @Test
    fun testStackMergeWithContext() = runTest {
        launchCoroutine()
        awaitCoroutineStarted()
        verifyDump(
            "Coroutine \"coroutine#2\":StandaloneCoroutine{Active}@50284dc4, state: RUNNING\n" +
                    "\tat jdk.internal.misc.Unsafe.park(Native Method)\n" +
                    "\tat java.util.concurrent.locks.LockSupport.park(LockSupport.java:175)\n" +
                    "\tat java.util.concurrent.locks.AbstractQueuedSynchronizer\$ConditionObject.await(AbstractQueuedSynchronizer.java:2039)\n" +
                    "\tat java.util.concurrent.CyclicBarrier.dowait(CyclicBarrier.java:234)\n" +
                    "\tat java.util.concurrent.CyclicBarrier.await(CyclicBarrier.java:362)\n" +
                    "\tat kotlinx.coroutines.debug.RunningThreadStackMergeTest.nonSuspendingFun(RunningThreadStackMergeTest.kt:86)\n" +
                    "\tat kotlinx.coroutines.debug.RunningThreadStackMergeTest.access\$nonSuspendingFun(RunningThreadStackMergeTest.kt:12)\n" +
                    "\tat kotlinx.coroutines.debug.RunningThreadStackMergeTest\$suspendingFunction\$2.invokeSuspend(RunningThreadStackMergeTest.kt:77)\n" +
                    "\tat kotlinx.coroutines.debug.RunningThreadStackMergeTest.suspendingFunction(RunningThreadStackMergeTest.kt:75)\n" +
                    "\tat kotlinx.coroutines.debug.RunningThreadStackMergeTest\$launchCoroutine\$1.invokeSuspend(RunningThreadStackMergeTest.kt:68)\n" +
                    "\tat _COROUTINE._CREATION._(CoroutineDebugging.kt)\n" +
                    "\tat kotlin.coroutines.intrinsics.IntrinsicsKt__IntrinsicsJvmKt.createCoroutineUnintercepted(IntrinsicsJvm.kt:116)",
            ignoredCoroutine = "BlockingCoroutine"
        ) {
            coroutineBlocker.await()
        }
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
        Thread.sleep(10)
        verifyDump(
            "Coroutine \"coroutine#2\":StandaloneCoroutine{Active}@3aea3c67, state: RUNNING\n" +
                    "\tat jdk.internal.misc.Unsafe.park(Native Method)\n" +
                    "\tat java.util.concurrent.locks.LockSupport.park(LockSupport.java:175)\n" +
                    "\tat java.util.concurrent.locks.AbstractQueuedSynchronizer\$ConditionObject.await(AbstractQueuedSynchronizer.java:2039)\n" +
                    "\tat java.util.concurrent.CyclicBarrier.dowait(CyclicBarrier.java:234)\n" +
                    "\tat java.util.concurrent.CyclicBarrier.await(CyclicBarrier.java:362)\n" +
                    "\tat kotlinx.coroutines.debug.RunningThreadStackMergeTest.nonSuspendingFun(RunningThreadStackMergeTest.kt:83)\n" +
                    "\tat kotlinx.coroutines.debug.RunningThreadStackMergeTest.access\$nonSuspendingFun(RunningThreadStackMergeTest.kt:12)\n" +
                    "\tat kotlinx.coroutines.debug.RunningThreadStackMergeTest\$suspendingFunctionWithContext\$2.invokeSuspend(RunningThreadStackMergeTest.kt:124)\n" +
                    "\tat kotlinx.coroutines.debug.RunningThreadStackMergeTest.suspendingFunctionWithContext(RunningThreadStackMergeTest.kt:122)\n" +
                    "\tat kotlinx.coroutines.debug.RunningThreadStackMergeTest\$launchEscapingCoroutine\$1.invokeSuspend(RunningThreadStackMergeTest.kt:116)\n" +
                    "\tat _COROUTINE._CREATION._(CoroutineDebugging.kt)\n" +
                    "\tat kotlin.coroutines.intrinsics.IntrinsicsKt__IntrinsicsJvmKt.createCoroutineUnintercepted(IntrinsicsJvm.kt:116)",
            ignoredCoroutine = "BlockingCoroutine"
        ) {
            coroutineBlocker.await()
        }
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

    @Test
    fun testMergeThroughInvokeSuspend() = runTest {
        launchEscapingCoroutineWithoutContext()
        awaitCoroutineStarted()
        verifyDump(
            "Coroutine \"coroutine#2\":StandaloneCoroutine{Active}@3aea3c67, state: RUNNING\n" +
                    "\tat jdk.internal.misc.Unsafe.park(Native Method)\n" +
                    "\tat java.util.concurrent.locks.LockSupport.park(LockSupport.java:175)\n" +
                    "\tat java.util.concurrent.locks.AbstractQueuedSynchronizer\$ConditionObject.await(AbstractQueuedSynchronizer.java:2039)\n" +
                    "\tat java.util.concurrent.CyclicBarrier.dowait(CyclicBarrier.java:234)\n" +
                    "\tat java.util.concurrent.CyclicBarrier.await(CyclicBarrier.java:362)\n" +
                    "\tat kotlinx.coroutines.debug.RunningThreadStackMergeTest.nonSuspendingFun(RunningThreadStackMergeTest.kt:83)\n" +
                    "\tat kotlinx.coroutines.debug.RunningThreadStackMergeTest.suspendingFunctionWithoutContext(RunningThreadStackMergeTest.kt:160)\n" +
                    "\tat kotlinx.coroutines.debug.RunningThreadStackMergeTest\$launchEscapingCoroutineWithoutContext\$1.invokeSuspend(RunningThreadStackMergeTest.kt:153)\n" +
                    "\tat _COROUTINE._CREATION._(CoroutineDebugging.kt)\n" +
                    "\tat kotlin.coroutines.intrinsics.IntrinsicsKt__IntrinsicsJvmKt.createCoroutineUnintercepted(IntrinsicsJvm.kt:116)",
            ignoredCoroutine = "BlockingCoroutine"
        ) {
            coroutineBlocker.await()
        }
    }

    private fun CoroutineScope.launchEscapingCoroutineWithoutContext() {
        launch(Dispatchers.IO) {
            suspendingFunctionWithoutContext()
            assertTrue(true)
        }
    }

    private suspend fun suspendingFunctionWithoutContext() {
        actualSuspensionPoint()
        nonSuspendingFun()
        assertTrue(true)
    }

    @Test
    fun testRunBlocking() = runBlocking {
        verifyDump("Coroutine \"coroutine#1\":BlockingCoroutine{Active}@4bcd176c, state: RUNNING\n" +
                "\tat java.lang.Thread.getStackTrace(Thread.java)\n" +
                "\tat kotlinx.coroutines.debug.internal.DebugProbesImpl.enhanceStackTraceWithThreadDumpImpl(DebugProbesImpl.kt)\n" +
                "\tat kotlinx.coroutines.debug.internal.DebugProbesImpl.dumpCoroutinesSynchronized(DebugProbesImpl.kt)\n" +
                "\tat kotlinx.coroutines.debug.internal.DebugProbesImpl.dumpCoroutines(DebugProbesImpl.kt)\n" +
                "\tat kotlinx.coroutines.debug.DebugProbes.dumpCoroutines(DebugProbes.kt)\n" +
                "\tat kotlinx.coroutines.debug.StacktraceUtilsKt.verifyDump(StacktraceUtils.kt)\n" +
                "\tat kotlinx.coroutines.debug.StacktraceUtilsKt.verifyDump\$default(StacktraceUtils.kt)\n" +
                "\tat kotlinx.coroutines.debug.RunningThreadStackMergeTest\$testRunBlocking\$1.invokeSuspend(RunningThreadStackMergeTest.kt)\n" +
                "\tat _COROUTINE._CREATION._(CoroutineDebugging.kt)\n" +
                "\tat kotlin.coroutines.intrinsics.IntrinsicsKt__IntrinsicsJvmKt.createCoroutineUnintercepted(IntrinsicsJvm.kt)\n")
    }


    private suspend fun actualSuspensionPoint() {
        nestedSuspensionPoint()
        assertTrue(true)
    }

    private suspend fun nestedSuspensionPoint() {
        yield()
        assertTrue(true)
    }

    @Test
    fun testActiveThread() = runBlocking<Unit> {
        launchCoroutine()
        awaitCoroutineStarted()
        val info = DebugProbesImpl.dumpDebuggerInfo().find { it.state == "RUNNING" }
        assertNotNull(info)
        assertNotNull(info.lastObservedThreadName)
        coroutineBlocker.await()
    }
}
