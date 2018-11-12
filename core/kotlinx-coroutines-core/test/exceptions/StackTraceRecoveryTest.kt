/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.exceptions

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.junit.Test
import java.io.*
import java.util.concurrent.*
import kotlin.test.*

/*
 * All stacktrace validation skips line numbers
 */
class StackTraceRecoveryTest : TestBase() {

    @Test
    fun testAsync() = runTest {
        fun createDeferred(depth: Int): Deferred<*> {
            return if (depth == 0) {
                async(coroutineContext + NonCancellable) {
                    throw ExecutionException(null)
                }
            } else {
                createDeferred(depth - 1)
            }
        }

        val deferred = createDeferred(3)
        val traces = listOf(
            "java.util.concurrent.ExecutionException\n" +
                    "\t(Current coroutine stacktrace)\n" +
                    "\tat kotlinx.coroutines.DeferredCoroutine.await\$suspendImpl(Builders.common.kt:99)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest.oneMoreNestedMethod(StackTraceRecoveryTest.kt:49)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest.nestedMethod(StackTraceRecoveryTest.kt:44)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testAsync\$1.invokeSuspend(StackTraceRecoveryTest.kt:17)\n",
            "Caused by: java.util.concurrent.ExecutionException\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testAsync\$1\$1\$1.invokeSuspend(StackTraceRecoveryTest.kt:21)\n" +
                    "\tat kotlin.coroutines.jvm.internal.BaseContinuationImpl.resumeWith(ContinuationImpl.kt:32)\n"
        )
        nestedMethod(deferred, traces)
        deferred.join()
    }

    @Test
    fun testCompletedAsync() = runTest {
        val deferred = async(coroutineContext + NonCancellable) {
            throw ExecutionException(null)
        }

        deferred.join()
        val stacktrace = listOf(
            "java.util.concurrent.ExecutionException\n" +
                    "\t(Current coroutine stacktrace)\n" +
                    "\tat kotlinx.coroutines.DeferredCoroutine.await\$suspendImpl(Builders.common.kt:99)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest.oneMoreNestedMethod(StackTraceRecoveryTest.kt:81)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest.nestedMethod(StackTraceRecoveryTest.kt:75)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testCompletedAsync\$1.invokeSuspend(StackTraceRecoveryTest.kt:71)",
            "Caused by: java.util.concurrent.ExecutionException\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testCompletedAsync\$1\$deferred\$1.invokeSuspend(StackTraceRecoveryTest.kt:44)\n" +
                    "\tat kotlin.coroutines.jvm.internal.BaseContinuationImpl.resumeWith(ContinuationImpl.kt:32)"
        )
        nestedMethod(deferred, stacktrace)
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

    @Test
    fun testReceiveFromChannel() = runTest {
        val channel = Channel<Int>()
        val job = launch {
            expect(2)
            channel.close(IllegalArgumentException())
        }

        expect(1)
        channelNestedMethod(
            channel, listOf(
                "java.lang.IllegalArgumentException\n" +
                        "\t(Current coroutine stacktrace)\n" +
                        "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest.channelNestedMethod(StackTraceRecoveryTest.kt:110)\n" +
                        "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testReceiveFromChannel\$1.invokeSuspend(StackTraceRecoveryTest.kt:89)",
                "Caused by: java.lang.IllegalArgumentException\n" +
                        "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testReceiveFromChannel\$1\$job\$1.invokeSuspend(StackTraceRecoveryTest.kt:93)\n" +
                        "\tat kotlin.coroutines.jvm.internal.BaseContinuationImpl.resumeWith(ContinuationImpl.kt:32)\n" +
                        "\tat kotlinx.coroutines.DispatchedTask\$DefaultImpls.run(Dispatched.kt:152)"
            )
        )
        expect(3)
        job.join()
        finish(4)
    }

    @Test
    fun testReceiveFromClosedChannel() = runTest {
        val channel = Channel<Int>()
        channel.close(IllegalArgumentException())
        channelNestedMethod(
            channel, listOf(
                "java.lang.IllegalArgumentException\n" +
                        "\t(Current coroutine stacktrace)\n" +
                        "\tat kotlinx.coroutines.channels.AbstractChannel.receiveResult(AbstractChannel.kt:574)\n" +
                        "\tat kotlinx.coroutines.channels.AbstractChannel.receive(AbstractChannel.kt:567)\n" +
                        "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest.channelNestedMethod(StackTraceRecoveryTest.kt:117)\n" +
                        "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testReceiveFromClosedChannel\$1.invokeSuspend(StackTraceRecoveryTest.kt:111)\n" +
                        "\tat kotlin.coroutines.jvm.internal.BaseContinuationImpl.resumeWith(ContinuationImpl.kt:32)",
                "Caused by: java.lang.IllegalArgumentException\n" +
                        "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testReceiveFromClosedChannel\$1.invokeSuspend(StackTraceRecoveryTest.kt:110)"
            )
        )
    }

    private suspend fun channelNestedMethod(channel: Channel<Int>, traces: List<String>) {
        try {
            channel.receive()
            expectUnreached()
        } catch (e: IllegalArgumentException) {
            verifyStackTrace(e, traces)
        }
    }

    @Test
    fun testWithContext() = runTest {
        val deferred = async(NonCancellable, start = CoroutineStart.LAZY) {
            throw RecoverableTestException()
        }

        outerMethod(deferred, listOf(
            "kotlinx.coroutines.RecoverableTestException\n" +
                "\t(Current coroutine stacktrace)\n" +
                "\tat kotlinx.coroutines.DeferredCoroutine.await\$suspendImpl(Builders.common.kt:99)\n" +
                "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest.innerMethod(StackTraceRecoveryTest.kt:158)\n" +
                "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$outerMethod\$2.invokeSuspend(StackTraceRecoveryTest.kt:151)\n" +
                "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest.outerMethod(StackTraceRecoveryTest.kt:150)\n" +
                "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testWithContext\$1.invokeSuspend(StackTraceRecoveryTest.kt:141)\n",
            "Caused by: kotlinx.coroutines.RecoverableTestException\n" +
                "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testWithContext\$1\$deferred\$1.invokeSuspend(StackTraceRecoveryTest.kt:143)\n" +
                "\tat kotlin.coroutines.jvm.internal.BaseContinuationImpl.resumeWith(ContinuationImpl.kt:32)\n"))
        deferred.join()
    }

    private suspend fun outerMethod(deferred: Deferred<Nothing>, traces: List<String>) {
        withContext(Dispatchers.IO) {
            innerMethod(deferred, traces)
        }

        assertTrue(true)
    }

    private suspend fun innerMethod(deferred: Deferred<Nothing>, traces: List<String>) {
        try {
            deferred.await()
        } catch (e: RecoverableTestException) {
            verifyStackTrace(e, traces)
        }
    }

    @Test
    fun testCoroutineScope() = runTest {
        val deferred = async(NonCancellable, start = CoroutineStart.LAZY) {
            throw RecoverableTestException()
        }

        outerScopedMethod(deferred, listOf(
            "kotlinx.coroutines.RecoverableTestException\n" +
                    "\t(Current coroutine stacktrace)\n" +
                    "\tat kotlinx.coroutines.DeferredCoroutine.await\$suspendImpl(Builders.common.kt:99)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest.innerMethod(StackTraceRecoveryTest.kt:158)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$outerScopedMethod\$2.invokeSuspend(StackTraceRecoveryTest.kt:151)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testCoroutineScope\$1.invokeSuspend(StackTraceRecoveryTest.kt:141)\n",
            "Caused by: kotlinx.coroutines.RecoverableTestException\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testCoroutineScope\$1\$deferred\$1.invokeSuspend(StackTraceRecoveryTest.kt:143)\n" +
                    "\tat kotlin.coroutines.jvm.internal.BaseContinuationImpl.resumeWith(ContinuationImpl.kt:32)\n"))
        deferred.join()
    }

    private suspend fun outerScopedMethod(deferred: Deferred<Nothing>, traces: List<String>) = coroutineScope {
        innerMethod(deferred, traces)
        assertTrue(true)
    }

    private fun verifyStackTrace(e: Throwable, traces: List<String>) {
        val stacktrace = toStackTrace(e)
        traces.forEach {
            assertTrue(
                stacktrace.trimStackTrace().contains(it.trimStackTrace()),
                "\nExpected trace element:\n$it\n\nActual stacktrace:\n$stacktrace"
            )
        }

        val causes = stacktrace.count("Caused by")
        assertNotEquals(0, causes)
        assertEquals(traces.map { it.count("Caused by") }.sum(), causes)
    }

    private fun toStackTrace(t: Throwable): String {
        val sw = StringWriter() as Writer
        t.printStackTrace(PrintWriter(sw))
        return sw.toString()
    }

    private fun String.trimStackTrace(): String {
        return applyBackspace(trimIndent().replace(Regex(":[0-9]+"), "")
            .replace("kotlinx_coroutines_core_main", "") // yay source sets
            .replace("kotlinx_coroutines_core", ""))
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
