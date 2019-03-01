/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug

import kotlinx.coroutines.*
import kotlinx.coroutines.debug.junit4.*
import org.junit.*
import org.junit.Test
import kotlin.coroutines.*
import kotlin.test.*

class CoroutinesDumpTest : DebugTestBase() {
    private val monitor = Any()

    @Test
    fun testSuspendedCoroutine() = synchronized(monitor) {
        val deferred = GlobalScope.async {
            sleepingOuterMethod()
        }

        awaitCoroutineStarted()
        Thread.sleep(100)  // Let delay be invoked
        verifyDump(
            "Coroutine \"coroutine#1\":DeferredCoroutine{Active}@1e4a7dd4, state: SUSPENDED\n" +
                "\tat kotlinx.coroutines.debug.CoroutinesDumpTest.sleepingNestedMethod(CoroutinesDumpTest.kt:95)\n" +
                "\tat kotlinx.coroutines.debug.CoroutinesDumpTest.sleepingOuterMethod(CoroutinesDumpTest.kt:88)\n" +
                "\tat kotlinx.coroutines.debug.CoroutinesDumpTest\$testSuspendedCoroutine\$1\$deferred\$1.invokeSuspend(CoroutinesDumpTest.kt:29)\n" +
            "\t(Coroutine creation stacktrace)\n" +
                "\tat kotlin.coroutines.intrinsics.IntrinsicsKt__IntrinsicsJvmKt.createCoroutineUnintercepted(IntrinsicsJvm.kt:116)\n" +
                "\tat kotlinx.coroutines.intrinsics.CancellableKt.startCoroutineCancellable(Cancellable.kt:23)\n" +
                "\tat kotlinx.coroutines.CoroutineStart.invoke(CoroutineStart.kt:99)\n")

        val found = DebugProbes.dumpCoroutinesState().single { it.jobOrNull === deferred }
        assertSame(deferred, found.jobOrNull)
        runBlocking { deferred.cancelAndJoin() }
    }

    @Test
    fun testRunningCoroutine() = synchronized(monitor) {
        val deferred = GlobalScope.async {
            activeMethod(shouldSuspend = false)
        }

        awaitCoroutineStarted()
        verifyDump(
            "Coroutine \"coroutine#1\":DeferredCoroutine{Active}@1e4a7dd4, state: RUNNING (Last suspension stacktrace, not an actual stacktrace)\n" +
                    "\tat kotlinx.coroutines.debug.CoroutinesDumpTest\$testRunningCoroutine\$1\$deferred\$1.invokeSuspend(CoroutinesDumpTest.kt:49)\n" +
             "\t(Coroutine creation stacktrace)\n" +
                    "\tat kotlin.coroutines.intrinsics.IntrinsicsKt__IntrinsicsJvmKt.createCoroutineUnintercepted(IntrinsicsJvm.kt:116)\n" +
                    "\tat kotlinx.coroutines.intrinsics.CancellableKt.startCoroutineCancellable(Cancellable.kt:23)\n" +
                    "\tat kotlinx.coroutines.CoroutineStart.invoke(CoroutineStart.kt:99)\n" +
                    "\tat kotlinx.coroutines.AbstractCoroutine.start(AbstractCoroutine.kt:148)\n" +
                    "\tat kotlinx.coroutines.BuildersKt__Builders_commonKt.async(Builders.common.kt)\n" +
                    "\tat kotlinx.coroutines.BuildersKt.async(Unknown Source)\n" +
                    "\tat kotlinx.coroutines.BuildersKt__Builders_commonKt.async\$default(Builders.common.kt)\n" +
                    "\tat kotlinx.coroutines.BuildersKt.async\$default(Unknown Source)\n" +
                    "\tat kotlinx.coroutines.debug.CoroutinesDumpTest.testRunningCoroutine(CoroutinesDumpTest.kt:49)")
        runBlocking { deferred.cancelAndJoin() }
    }

    @Test
    fun testRunningCoroutineWithSuspensionPoint() = synchronized(monitor) {
        val deferred = GlobalScope.async {
            activeMethod(shouldSuspend = true)
            yield() // tail-call
        }

        awaitCoroutineStarted()
        Thread.sleep(10)
        verifyDump(
            "Coroutine \"coroutine#1\":DeferredCoroutine{Active}@1e4a7dd4, state: RUNNING\n" +
                "\tat java.lang.Thread.sleep(Native Method)\n" +
                "\tat kotlinx.coroutines.debug.CoroutinesDumpTest.nestedActiveMethod(CoroutinesDumpTest.kt:111)\n" +
                "\tat kotlinx.coroutines.debug.CoroutinesDumpTest.activeMethod(CoroutinesDumpTest.kt:106)\n" +
                "\tat kotlinx.coroutines.debug.CoroutinesDumpTest\$testRunningCoroutineWithSuspensionPoint\$1\$deferred\$1.invokeSuspend(CoroutinesDumpTest.kt:71)\n" +
                "\t(Coroutine creation stacktrace)\n" +
                "\tat kotlin.coroutines.intrinsics.IntrinsicsKt__IntrinsicsJvmKt.createCoroutineUnintercepted(IntrinsicsJvm.kt:116)\n" +
                "\tat kotlinx.coroutines.intrinsics.CancellableKt.startCoroutineCancellable(Cancellable.kt:23)\n" +
                "\tat kotlinx.coroutines.CoroutineStart.invoke(CoroutineStart.kt:99)\n" +
                "\tat kotlinx.coroutines.AbstractCoroutine.start(AbstractCoroutine.kt:148)\n" +
                "\tat kotlinx.coroutines.BuildersKt__Builders_commonKt.async(Builders.common.kt)\n" +
                "\tat kotlinx.coroutines.BuildersKt.async(Unknown Source)\n" +
                "\tat kotlinx.coroutines.BuildersKt__Builders_commonKt.async\$default(Builders.common.kt)\n" +
                "\tat kotlinx.coroutines.BuildersKt.async\$default(Unknown Source)\n" +
                "\tat kotlinx.coroutines.debug.CoroutinesDumpTest.testRunningCoroutineWithSuspensionPoint(CoroutinesDumpTest.kt:71)"
        )
        runBlocking { deferred.cancelAndJoin() }
    }

    @Test
    fun testCreationStackTrace() = synchronized(monitor) {
        val deferred = GlobalScope.async {
            activeMethod(shouldSuspend = true)
        }

        awaitCoroutineStarted()
        val coroutine = DebugProbes.dumpCoroutinesState().first()
        val result = coroutine.creationStackTrace.fold(StringBuilder()) { acc, element ->
            acc.append(element.toString())
            acc.append('\n')
        }.toString().trimStackTrace()

        runBlocking { deferred.cancelAndJoin() }

        val expected = ("kotlin.coroutines.intrinsics.IntrinsicsKt__IntrinsicsJvmKt.createCoroutineUnintercepted(IntrinsicsJvm.kt:116)\n" +
                "kotlinx.coroutines.intrinsics.CancellableKt.startCoroutineCancellable(Cancellable.kt:23)\n" +
                "kotlinx.coroutines.CoroutineStart.invoke(CoroutineStart.kt:109)\n" +
                "kotlinx.coroutines.AbstractCoroutine.start(AbstractCoroutine.kt:160)\n" +
                "kotlinx.coroutines.BuildersKt__Builders_commonKt.async(Builders.common.kt:88)\n" +
                "kotlinx.coroutines.BuildersKt.async(Unknown Source)\n" +
                "kotlinx.coroutines.BuildersKt__Builders_commonKt.async\$default(Builders.common.kt:81)\n" +
                "kotlinx.coroutines.BuildersKt.async\$default(Unknown Source)\n" +
                "kotlinx.coroutines.debug.CoroutinesDumpTest.testCreationStackTrace(CoroutinesDumpTest.kt:109)").trimStackTrace()
        assertTrue(result.startsWith(expected))
    }

    @Test
    fun testFinishedCoroutineRemoved() = synchronized(monitor) {
        val deferred = GlobalScope.async {
            activeMethod(shouldSuspend = true)
        }

        awaitCoroutineStarted()
        runBlocking { deferred.cancelAndJoin() }
        verifyDump()
    }

    private suspend fun activeMethod(shouldSuspend: Boolean) {
        nestedActiveMethod(shouldSuspend)
        assertTrue(true) // tail-call
    }

    private suspend fun nestedActiveMethod(shouldSuspend: Boolean) {
        if (shouldSuspend) yield()
        notifyTest()
        while (coroutineContext[Job]!!.isActive) {
            Thread.sleep(100)
        }
    }

    private suspend fun sleepingOuterMethod() {
        sleepingNestedMethod()
        yield()
    }

    private suspend fun sleepingNestedMethod() {
        yield()
        notifyTest()
        delay(Long.MAX_VALUE)
    }

    private fun awaitCoroutineStarted() {
        (monitor as Object).wait()
    }

    private fun notifyTest() {
        synchronized(monitor) {
            (monitor as Object).notify()
        }
    }
}
