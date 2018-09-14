/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines

import org.junit.Test
import java.io.*
import java.util.concurrent.*
import kotlin.test.*

class DebugProbesTest : TestBase() {

    private fun CoroutineScope.createDeferred(): Deferred<*> = async {
        throw ExecutionException(null)
    }

    @Test
    fun testAsync() = runTest {

        val deferred = createDeferred()
        val traces = listOf(
            "java.util.concurrent.ExecutionException\n" +
                    "\t(Current coroutine stacktrace)\n" +
                    "\tat kotlinx/coroutines/DeferredCoroutine.await\$suspendImpl(Deferred.kt:234)\n" +
                    "\tat kotlinx/coroutines/DebugProbesTest.oneMoreNestedMethod(DebugProbesTest.kt:49)\n" +
                    "\tat kotlinx/coroutines/DebugProbesTest.nestedMethod(DebugProbesTest.kt:44)\n" +
                    "\tat kotlinx/coroutines/DebugProbesTest\$testAsync\$1.invokeSuspend(DebugProbesTest.kt:17)\n" +
                    "Caused by: java.util.concurrent.ExecutionException\n" +
                    "\tat kotlinx.coroutines.DebugProbesTest\$createDeferred\$1.invokeSuspend(DebugProbesTest.kt:16)\n" +
                    "\tat kotlin.coroutines.jvm.internal.BaseContinuationImpl.resumeWith(ContinuationImpl.kt:32)\n"
        )
        nestedMethod(deferred, traces)
        deferred.join()
    }

    @Test
    fun testAsyncWithProbes() = DebugProbes.withDebugProbes {
        runTest {
            val deferred = createDeferred()
            val traces = listOf(
                "java.util.concurrent.ExecutionException\n" +
                        "\t(Current coroutine stacktrace)\n" +
                        "\tat kotlinx/coroutines/DeferredCoroutine.await\$suspendImpl(Deferred.kt:234)\n" +
                        "\tat kotlinx/coroutines/DebugProbesTest.oneMoreNestedMethod(DebugProbesTest.kt:71)\n" +
                        "\tat kotlinx/coroutines/DebugProbesTest.nestedMethod(DebugProbesTest.kt:66)\n" +
                        "\tat kotlinx/coroutines/DebugProbesTest\$testAsyncWithProbes\$1\$1.invokeSuspend(DebugProbesTest.kt:43)\n" +
                        "\t(Coroutine creation callsite)\n" +
                        "\tat kotlin.coroutines.intrinsics.IntrinsicsKt__IntrinsicsJvmKt.createCoroutineUnintercepted(IntrinsicsJvm.kt:116)\n" +
                        "\tat kotlinx.coroutines.intrinsics.CancellableKt.startCoroutineCancellable(Cancellable.kt:23)\n" +
                        "\tat kotlinx.coroutines.CoroutineStart.invoke(CoroutineStart.kt:99)\n" +
                        "\tat kotlinx.coroutines.AbstractCoroutine.start(AbstractCoroutine.kt:148)\n" +
                        "\tat kotlinx.coroutines.BuildersKt__BuildersKt.runBlocking(Builders.kt:45)\n" +
                        "\tat kotlinx.coroutines.BuildersKt.runBlocking(Unknown Source)\n" +
                        "\tat kotlinx.coroutines.TestBase.runTest(TestBase.kt:138)\n" +
                        "\tat kotlinx.coroutines.TestBase.runTest\$default(TestBase.kt:19)\n" +
                        "\tat kotlinx.coroutines.DebugProbesTest.testAsyncWithProbes(DebugProbesTest.kt:38)",
                "Caused by: java.util.concurrent.ExecutionException\n" +
                        "\tat kotlinx.coroutines.DebugProbesTest\$createDeferred\$1.invokeSuspend(DebugProbesTest.kt:16)\n" +
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

    private fun verifyStackTrace(e: Throwable, traces: List<String>) {
        val stacktrace = toStackTrace(e)
        traces.forEach {
            assertTrue(stacktrace.trimStackTrace().contains(it.trimStackTrace()),
                "\nExpected trace element:\n$it\n\nActual stacktrace:\n$stacktrace")
        }

        val causes = stacktrace.count("Caused by")
        assertNotEquals(0, causes)
        assertEquals(causes, traces.map { it.count("Caused by") }.sum())
    }

    private fun toStackTrace(t: Throwable): String {
        val sw = StringWriter() as Writer
        t.printStackTrace(PrintWriter(sw))
        return sw.toString()
    }


    private fun String.trimStackTrace(): String {
        return applyBackspace(trimIndent().replace(Regex(":[0-9]+"), ""))
    }

    private fun applyBackspace(line: String): String {
        val array = line.toCharArray()
        val stack = CharArray(array.size)
        var stackSize = -1
        for (c in array) {
            if (c != '\b') {
                stack[++stackSize] = c
            } else {
                --stackSize
            }
        }

        return String(stack, 0, stackSize)
    }

    private fun String.count(substring: String): Int = split(substring).size - 1
}
