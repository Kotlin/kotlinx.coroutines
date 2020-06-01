/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines.debug

import kotlinx.coroutines.*
import org.junit.Test
import java.util.concurrent.*
import kotlin.test.*

class DebugProbesTest : DebugTestBase() {

    private fun CoroutineScope.createDeferred(): Deferred<*> = async(NonCancellable) {
        throw ExecutionException(null)
    }

    @Test
    fun testAsync() = runTest {
        val deferred = createDeferred()
        val traces = listOf(
            "java.util.concurrent.ExecutionException\n" +
                    "\tat kotlinx.coroutines.debug.DebugProbesTest\$createDeferred\$1.invokeSuspend(DebugProbesTest.kt:14)\n" +
                    "\t(Coroutine boundary)\n" +
                    "\tat kotlinx.coroutines.DeferredCoroutine.await\$suspendImpl(Builders.common.kt)\n" +
                    "\tat kotlinx.coroutines.debug.DebugProbesTest.oneMoreNestedMethod(DebugProbesTest.kt:49)\n" +
                    "\tat kotlinx.coroutines.debug.DebugProbesTest.nestedMethod(DebugProbesTest.kt:44)\n" +
                    "\tat kotlinx.coroutines.debug.DebugProbesTest\$testAsync\$1.invokeSuspend(DebugProbesTest.kt:17)\n",
            "Caused by: java.util.concurrent.ExecutionException\n" +
                    "\tat kotlinx.coroutines.debug.DebugProbesTest\$createDeferred\$1.invokeSuspend(DebugProbesTest.kt:14)\n" +
                    "\tat kotlin.coroutines.jvm.internal.BaseContinuationImpl.resumeWith(ContinuationImpl.kt:32)"
        )
        nestedMethod(deferred, traces)
        deferred.join()
    }

    @Test
    fun testAsyncWithProbes() = DebugProbes.withDebugProbes {
        DebugProbes.sanitizeStackTraces = false
        runTest {
            val deferred = createDeferred()
            val traces = listOf(
                "java.util.concurrent.ExecutionException\n" +
                        "\tat kotlinx.coroutines.debug.DebugProbesTest\$createDeferred\$1.invokeSuspend(DebugProbesTest.kt:16)\n" +
                        "\t(Coroutine boundary)\n" +
                        "\tat kotlinx.coroutines.DeferredCoroutine.await\$suspendImpl(Builders.common.kt)\n" +
                        "\tat kotlinx.coroutines.debug.DebugProbesTest.oneMoreNestedMethod(DebugProbesTest.kt:71)\n" +
                        "\tat kotlinx.coroutines.debug.DebugProbesTest.nestedMethod(DebugProbesTest.kt:66)\n" +
                    "\t(Coroutine creation stacktrace)\n" +
                        "\tat kotlin.coroutines.intrinsics.IntrinsicsKt__IntrinsicsJvmKt.createCoroutineUnintercepted(IntrinsicsJvm.kt:116)\n" +
                        "\tat kotlinx.coroutines.intrinsics.CancellableKt.startCoroutineCancellable(Cancellable.kt:26)\n" +
                        "\tat kotlinx.coroutines.BuildersKt__Builders_commonKt.startCoroutineImpl(Builders.common.kt:179)\n" +
                        "\tat kotlinx.coroutines.BuildersKt.startCoroutineImpl(Unknown Source)\n" +
                        "\tat kotlinx.coroutines.AbstractCoroutine.start(AbstractCoroutine.kt:145)\n" +
                        "\tat kotlinx.coroutines.BuildersKt__BuildersKt.runBlocking(Builders.kt:55)\n" +
                        "\tat kotlinx.coroutines.BuildersKt.runBlocking(Unknown Source)\n" +
                        "\tat kotlinx.coroutines.TestBase.runTest(TestBase.kt:188)\n" +
                        "\tat kotlinx.coroutines.TestBase.runTest\$default(TestBase.kt:182)\n" +
                        "\tat kotlinx.coroutines.debug.DebugProbesTest.testAsyncWithProbes(DebugProbesTest.kt:39)",
                "Caused by: java.util.concurrent.ExecutionException\n" +
                        "\tat kotlinx.coroutines.debug.DebugProbesTest\$createDeferred\$1.invokeSuspend(DebugProbesTest.kt:16)\n" +
                        "\tat kotlin.coroutines.jvm.internal.BaseContinuationImpl.resumeWith(ContinuationImpl.kt:32)\n")
            nestedMethod(deferred, traces)
            deferred.join()
        }
    }

    @Test
    fun testAsyncWithSanitizedProbes() = DebugProbes.withDebugProbes {
        DebugProbes.sanitizeStackTraces = true
        runTest {
            val deferred = createDeferred()
            val traces = listOf(
                "java.util.concurrent.ExecutionException\n" +
                        "\tat kotlinx.coroutines.debug.DebugProbesTest\$createDeferred\$1.invokeSuspend(DebugProbesTest.kt:16)\n" +
                        "\t(Coroutine boundary)\n" +
                        "\tat kotlinx.coroutines.DeferredCoroutine.await\$suspendImpl(Builders.common.kt)\n" +
                        "\tat kotlinx.coroutines.debug.DebugProbesTest.oneMoreNestedMethod(DebugProbesTest.kt:71)\n" +
                        "\tat kotlinx.coroutines.debug.DebugProbesTest.nestedMethod(DebugProbesTest.kt:66)\n" +
                        "\t(Coroutine creation stacktrace)\n" +
                        "\tat kotlin.coroutines.intrinsics.IntrinsicsKt__IntrinsicsJvmKt.createCoroutineUnintercepted(IntrinsicsJvm.kt:116)\n" +
                        "\tat kotlinx.coroutines.intrinsics.CancellableKt.startCoroutineCancellable(Cancellable.kt:23)\n" +
                        "\tat kotlinx.coroutines.debug.DebugProbesTest.testAsyncWithSanitizedProbes(DebugProbesTest.kt:38)",
                "Caused by: java.util.concurrent.ExecutionException\n" +
                        "\tat kotlinx.coroutines.debug.DebugProbesTest\$createDeferred\$1.invokeSuspend(DebugProbesTest.kt:16)\n" +
                        "\tat kotlin.coroutines.jvm.internal.BaseContinuationImpl.resumeWith(ContinuationImpl.kt:32)\n")
            nestedMethod(deferred, traces)
            deferred.join()
        }
    }

    private suspend fun nestedMethod(deferred: Deferred<*>, traces: List<String>) {
        oneMoreNestedMethod(deferred, traces)
        assertTrue(true) // Prevent tail-call optimization
    }

    private suspend fun oneMoreNestedMethod(deferred: Deferred<*>, traces: List<String>) {
        try {
            deferred.await()
            expectUnreached()
        } catch (e: ExecutionException) {
            verifyStackTrace(e, traces)
        }
    }
}
