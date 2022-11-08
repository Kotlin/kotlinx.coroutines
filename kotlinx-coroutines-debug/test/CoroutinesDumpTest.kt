/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug

import kotlinx.coroutines.*
import org.junit.Test
import kotlin.coroutines.*
import kotlin.test.*

class CoroutinesDumpTest : DebugTestBase() {
    private val monitor = Any()
    private var coroutineThread: Thread? = null // guarded by monitor

    @Test
    fun testSuspendedCoroutine() = runBlocking {
        val deferred = async(Dispatchers.Default) {
            sleepingOuterMethod()
        }

        awaitCoroutine()
        val found = DebugProbes.dumpCoroutinesInfo().single { it.job === deferred }
        verifyDump(
            "Coroutine \"coroutine#1\":DeferredCoroutine{Active}@1e4a7dd4, state: SUSPENDED\n" +
                    "\tat kotlinx.coroutines.debug.CoroutinesDumpTest.sleepingNestedMethod(CoroutinesDumpTest.kt:95)\n" +
                    "\tat kotlinx.coroutines.debug.CoroutinesDumpTest.sleepingOuterMethod(CoroutinesDumpTest.kt:88)\n" +
                    "\tat _COROUTINE._CREATION._(CoroutineDebugging.kt)\n" +
                    "\tat kotlin.coroutines.intrinsics.IntrinsicsKt__IntrinsicsJvmKt.createCoroutineUnintercepted(IntrinsicsJvm.kt:116)\n" +
                    "\tat kotlinx.coroutines.intrinsics.CancellableKt.startCoroutineCancellable(Cancellable.kt:23)\n" +
                    "\tat kotlinx.coroutines.CoroutineStart.invoke(CoroutineStart.kt:99)\n",
            ignoredCoroutine = "BlockingCoroutine"
        ) {
            deferred.cancel()
            coroutineThread!!.interrupt()
        }
        assertSame(deferred, found.job)
    }

    @Test
    fun testRunningCoroutine() = runBlocking {
        val deferred = async(Dispatchers.IO) {
            activeMethod(shouldSuspend = false)
            assertTrue(true)
        }

        awaitCoroutine()
        verifyDump(
            "Coroutine \"coroutine#1\":DeferredCoroutine{Active}@227d9994, state: RUNNING\n" +
                    "\tat java.lang.Thread.sleep(Native Method)\n" +
                    "\tat kotlinx.coroutines.debug.CoroutinesDumpTest.nestedActiveMethod(CoroutinesDumpTest.kt:141)\n" +
                    "\tat kotlinx.coroutines.debug.CoroutinesDumpTest.activeMethod(CoroutinesDumpTest.kt:133)\n" +
                    "\tat kotlinx.coroutines.debug.CoroutinesDumpTest\$testRunningCoroutine\$1$deferred\$1.invokeSuspend(CoroutinesDumpTest.kt:41)\n" +
                    "\tat _COROUTINE._CREATION._(CoroutineDebugging.kt)\n" +
                    "\tat kotlin.coroutines.intrinsics.IntrinsicsKt__IntrinsicsJvmKt.createCoroutineUnintercepted(IntrinsicsJvm.kt:116)\n" +
                    "\tat kotlinx.coroutines.intrinsics.CancellableKt.startCoroutineCancellable(Cancellable.kt:23)\n" +
                    "\tat kotlinx.coroutines.CoroutineStart.invoke(CoroutineStart.kt:99)\n" +
                    "\tat kotlinx.coroutines.AbstractCoroutine.start(AbstractCoroutine.kt:148)\n" +
                    "\tat kotlinx.coroutines.BuildersKt__Builders_commonKt.async(Builders.common.kt)\n" +
                    "\tat kotlinx.coroutines.BuildersKt.async(Unknown Source)\n" +
                    "\tat kotlinx.coroutines.BuildersKt__Builders_commonKt.async\$default(Builders.common.kt)\n" +
                    "\tat kotlinx.coroutines.BuildersKt.async\$default(Unknown Source)\n" +
                    "\tat kotlinx.coroutines.debug.CoroutinesDumpTest.testRunningCoroutine(CoroutinesDumpTest.kt:49)",
            ignoredCoroutine = "BlockingCoroutine"
        ) {
            deferred.cancel()
            coroutineThread?.interrupt()
        }
    }

    @Test
    fun testRunningCoroutineWithSuspensionPoint() = runBlocking {
        val deferred = async(Dispatchers.IO) {
            activeMethod(shouldSuspend = true)
            yield() // tail-call
        }

        awaitCoroutine()
        verifyDump(
            "Coroutine \"coroutine#1\":DeferredCoroutine{Active}@1e4a7dd4, state: RUNNING\n" +
                    "\tat java.lang.Thread.sleep(Native Method)\n" +
                    "\tat kotlinx.coroutines.debug.CoroutinesDumpTest.nestedActiveMethod(CoroutinesDumpTest.kt:111)\n" +
                    "\tat kotlinx.coroutines.debug.CoroutinesDumpTest.activeMethod(CoroutinesDumpTest.kt:106)\n" +
                    "\tat _COROUTINE._CREATION._(CoroutineDebugging.kt)\n" +
                    "\tat kotlin.coroutines.intrinsics.IntrinsicsKt__IntrinsicsJvmKt.createCoroutineUnintercepted(IntrinsicsJvm.kt:116)\n" +
                    "\tat kotlinx.coroutines.intrinsics.CancellableKt.startCoroutineCancellable(Cancellable.kt:23)\n" +
                    "\tat kotlinx.coroutines.CoroutineStart.invoke(CoroutineStart.kt:99)\n" +
                    "\tat kotlinx.coroutines.AbstractCoroutine.start(AbstractCoroutine.kt:148)\n" +
                    "\tat kotlinx.coroutines.BuildersKt__Builders_commonKt.async(Builders.common.kt)\n" +
                    "\tat kotlinx.coroutines.BuildersKt.async(Unknown Source)\n" +
                    "\tat kotlinx.coroutines.BuildersKt__Builders_commonKt.async\$default(Builders.common.kt)\n" +
                    "\tat kotlinx.coroutines.BuildersKt.async\$default(Unknown Source)\n" +
                    "\tat kotlinx.coroutines.debug.CoroutinesDumpTest.testRunningCoroutineWithSuspensionPoint(CoroutinesDumpTest.kt:71)",
            ignoredCoroutine = "BlockingCoroutine"
        ) {
            deferred.cancel()
            coroutineThread!!.interrupt()
        }
    }

    @Test
    fun testCreationStackTrace() = runBlocking {
        val deferred = async(Dispatchers.IO) {
            activeMethod(shouldSuspend = true)
        }

        awaitCoroutine()
        val coroutine = DebugProbes.dumpCoroutinesInfo().first { it.job is Deferred<*> }
        val result = coroutine.creationStackTrace.fold(StringBuilder()) { acc, element ->
            acc.append(element.toString())
            acc.append('\n')
        }.toString().trimStackTrace()

        deferred.cancel()
        coroutineThread!!.interrupt()

        val expected =
            "kotlin.coroutines.intrinsics.IntrinsicsKt__IntrinsicsJvmKt.createCoroutineUnintercepted(IntrinsicsJvm.kt)\n" +
            "kotlinx.coroutines.intrinsics.CancellableKt.startCoroutineCancellable(Cancellable.kt)\n" +
            "kotlinx.coroutines.intrinsics.CancellableKt.startCoroutineCancellable\$default(Cancellable.kt)\n" +
            "kotlinx.coroutines.CoroutineStart.invoke(CoroutineStart.kt)\n" +
            "kotlinx.coroutines.AbstractCoroutine.start(AbstractCoroutine.kt)\n" +
            "kotlinx.coroutines.BuildersKt__Builders_commonKt.async(Builders.common.kt)\n" +
            "kotlinx.coroutines.BuildersKt.async(Unknown Source)\n" +
            "kotlinx.coroutines.BuildersKt__Builders_commonKt.async\$default(Builders.common.kt)\n" +
            "kotlinx.coroutines.BuildersKt.async\$default(Unknown Source)\n" +
            "kotlinx.coroutines.debug.CoroutinesDumpTest\$testCreationStackTrace\$1.invokeSuspend(CoroutinesDumpTest.kt)"
        if (!result.startsWith(expected)) {
            println("=== Actual result")
            println(result)
            error("Does not start with expected lines")
        }

    }

    @Test
    fun testFinishedCoroutineRemoved() = runBlocking {
        val deferred = async(Dispatchers.IO) {
            activeMethod(shouldSuspend = true)
        }

        awaitCoroutine()
        deferred.cancel()
        coroutineThread!!.interrupt()
        deferred.join()
        verifyDump(ignoredCoroutine = "BlockingCoroutine")
    }

    private suspend fun activeMethod(shouldSuspend: Boolean) {
        nestedActiveMethod(shouldSuspend)
        assertTrue(true) // tail-call
    }

    private suspend fun nestedActiveMethod(shouldSuspend: Boolean) {
        if (shouldSuspend) yield()
        notifyCoroutineStarted()
        while (coroutineContext[Job]!!.isActive) {
            try {
                Thread.sleep(60_000)
            } catch (_ : InterruptedException) {
            }
        }
    }

    private suspend fun sleepingOuterMethod() {
        sleepingNestedMethod()
        yield() // TCE
    }

    private suspend fun sleepingNestedMethod() {
        yield() // Suspension point
        notifyCoroutineStarted()
        delay(Long.MAX_VALUE)
    }

    private fun awaitCoroutine() = synchronized(monitor) {
        while (coroutineThread == null) (monitor as Object).wait()
        while (coroutineThread!!.state != Thread.State.TIMED_WAITING) {
            // Wait until thread sleeps to have a consistent stacktrace
        }
    }

    private fun notifyCoroutineStarted() {
        synchronized(monitor) {
            coroutineThread = Thread.currentThread()
            (monitor as Object).notifyAll()
        }
    }
}
