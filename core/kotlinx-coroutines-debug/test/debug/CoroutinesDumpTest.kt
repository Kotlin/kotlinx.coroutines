/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug

import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import java.io.*
import kotlin.coroutines.*
import kotlin.test.*

@Suppress("SUSPENSION_POINT_INSIDE_MONITOR") // bug in 1.3.0 FE
class CoroutinesDumpTest : TestBase() {

    private val monitor = Any()

    @Before
    fun setUp() {
        before()
        DebugProbes.sanitizeStackTraces = false
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
        assertSame(deferred, found.job)
        deferred.cancel()
        runBlocking { deferred.join() }
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
        deferred.cancel()
        runBlocking { deferred.join() }
    }

    @Test
    fun testRunningCoroutineWithSuspensionPoint() = synchronized(monitor) {
        val deferred = GlobalScope.async {
            activeMethod(shouldSuspend = true)
        }

        awaitCoroutineStarted()
        verifyDump(
           "Coroutine \"coroutine#1\":DeferredCoroutine{Active}@1e4a7dd4, state: RUNNING (Last suspension stacktrace, not an actual stacktrace)\n" +
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
                   "\tat kotlinx.coroutines.debug.CoroutinesDumpTest.testRunningCoroutineWithSuspensionPoint(CoroutinesDumpTest.kt:71)")
        deferred.cancel()
        runBlocking { deferred.join() }
    }

    @Test
    fun testFinishedCoroutineRemoved() = synchronized(monitor) {
        val deferred = GlobalScope.async {
            activeMethod(shouldSuspend = true)
        }

        awaitCoroutineStarted()
        deferred.cancel()
        runBlocking { deferred.join() }
        verifyDump()
    }

    private suspend fun activeMethod(shouldSuspend: Boolean) {
        nestedActiveMethod(shouldSuspend)
        delay(1)
    }

    private suspend fun nestedActiveMethod(shouldSuspend: Boolean) {
        if (shouldSuspend) delay(1)
        notifyTest()
        while (coroutineContext[Job]!!.isActive) {
            Thread.sleep(100)
        }
    }

    private suspend fun sleepingOuterMethod() {
        sleepingNestedMethod()
        delay(1)
    }

    private suspend fun sleepingNestedMethod() {
        delay(1)
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
