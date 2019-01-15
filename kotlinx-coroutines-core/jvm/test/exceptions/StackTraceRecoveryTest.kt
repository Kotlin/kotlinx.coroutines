/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.exceptions

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.selects.*
import org.junit.Test
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
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testAsync\$1\$1\$1.invokeSuspend(StackTraceRecoveryTest.kt:99)\n" +
                    "\t(Coroutine boundary)\n" +
                    "\tat kotlinx.coroutines.DeferredCoroutine.await\$suspendImpl(Builders.common.kt:99)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest.oneMoreNestedMethod(StackTraceRecoveryTest.kt:49)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest.nestedMethod(StackTraceRecoveryTest.kt:44)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testAsync\$1.invokeSuspend(StackTraceRecoveryTest.kt:17)\n",
            "Caused by: java.util.concurrent.ExecutionException\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testAsync\$1\$1\$1.invokeSuspend(StackTraceRecoveryTest.kt:21)\n" +
                    "\tat kotlin.coroutines.jvm.internal.BaseContinuationImpl.resumeWith(ContinuationImpl.kt:32)\n"
        )
        nestedMethod(deferred, *traces.toTypedArray())
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
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testCompletedAsync\$1\$deferred\$1.invokeSuspend(StackTraceRecoveryTest.kt:44)\n" +
                    "\t(Coroutine boundary)\n" +
                    "\tat kotlinx.coroutines.DeferredCoroutine.await\$suspendImpl(Builders.common.kt:99)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest.oneMoreNestedMethod(StackTraceRecoveryTest.kt:81)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest.nestedMethod(StackTraceRecoveryTest.kt:75)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testCompletedAsync\$1.invokeSuspend(StackTraceRecoveryTest.kt:71)",
            "Caused by: java.util.concurrent.ExecutionException\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testCompletedAsync\$1\$deferred\$1.invokeSuspend(StackTraceRecoveryTest.kt:44)\n" +
                    "\tat kotlin.coroutines.jvm.internal.BaseContinuationImpl.resumeWith(ContinuationImpl.kt:32)"
        )
        nestedMethod(deferred, *stacktrace.toTypedArray())
    }

    private suspend fun nestedMethod(deferred: Deferred<*>, vararg traces: String) {
        oneMoreNestedMethod(deferred, *traces)
        assertTrue(true) // Prevent tail-call optimization
    }

    private suspend fun oneMoreNestedMethod(deferred: Deferred<*>, vararg traces: String) {
        try {
            deferred.await()
            expectUnreached()
        } catch (e: ExecutionException) {
            verifyStackTrace(e, *traces)
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
            channel,
                "java.lang.IllegalArgumentException\n" +
                        "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testReceiveFromChannel\$1\$job\$1.invokeSuspend(StackTraceRecoveryTest.kt:93)\n" +
                        "\t(Coroutine boundary)\n" +
                        "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest.channelNestedMethod(StackTraceRecoveryTest.kt:110)\n" +
                        "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testReceiveFromChannel\$1.invokeSuspend(StackTraceRecoveryTest.kt:89)",
                "Caused by: java.lang.IllegalArgumentException\n" +
                        "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testReceiveFromChannel\$1\$job\$1.invokeSuspend(StackTraceRecoveryTest.kt:93)\n" +
                        "\tat kotlin.coroutines.jvm.internal.BaseContinuationImpl.resumeWith(ContinuationImpl.kt:32)\n" +
                        "\tat kotlinx.coroutines.DispatchedTask.run(Dispatched.kt:152)")
        expect(3)
        job.join()
        finish(4)
    }

    @Test
    fun testReceiveFromClosedChannel() = runTest {
        val channel = Channel<Int>()
        channel.close(IllegalArgumentException())
        channelNestedMethod(
            channel,
                "java.lang.IllegalArgumentException\n" +
                        "\t(Coroutine boundary)\n" +
                        "\tat kotlinx.coroutines.channels.AbstractChannel.receiveResult(AbstractChannel.kt:574)\n" +
                        "\tat kotlinx.coroutines.channels.AbstractChannel.receive(AbstractChannel.kt:567)\n" +
                        "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest.channelNestedMethod(StackTraceRecoveryTest.kt:117)\n" +
                        "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testReceiveFromClosedChannel\$1.invokeSuspend(StackTraceRecoveryTest.kt:111)\n",
                "Caused by: java.lang.IllegalArgumentException\n" +
                        "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testReceiveFromClosedChannel\$1.invokeSuspend(StackTraceRecoveryTest.kt:110)")
    }

    private suspend fun channelNestedMethod(channel: Channel<Int>, vararg traces: String) {
        try {
            channel.receive()
            expectUnreached()
        } catch (e: IllegalArgumentException) {
            verifyStackTrace(e, *traces)
        }
    }

    @Test
    fun testWithContext() = runTest {
        val deferred = async(NonCancellable, start = CoroutineStart.LAZY) {
            throw RecoverableTestException()
        }

        outerMethod(deferred,
            "kotlinx.coroutines.RecoverableTestException\n" +
                "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testWithContext\$1\$deferred\$1.invokeSuspend(StackTraceRecoveryTest.kt:143)\n" +
                "\t(Coroutine boundary)\n" +
                "\tat kotlinx.coroutines.DeferredCoroutine.await\$suspendImpl(Builders.common.kt:99)\n" +
                "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest.innerMethod(StackTraceRecoveryTest.kt:158)\n" +
                "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$outerMethod\$2.invokeSuspend(StackTraceRecoveryTest.kt:151)\n" +
                "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest.outerMethod(StackTraceRecoveryTest.kt:150)\n" +
                "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testWithContext\$1.invokeSuspend(StackTraceRecoveryTest.kt:141)\n",
            "Caused by: kotlinx.coroutines.RecoverableTestException\n" +
                "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testWithContext\$1\$deferred\$1.invokeSuspend(StackTraceRecoveryTest.kt:143)\n" +
                "\tat kotlin.coroutines.jvm.internal.BaseContinuationImpl.resumeWith(ContinuationImpl.kt:32)\n")
        deferred.join()
    }

    private suspend fun outerMethod(deferred: Deferred<Nothing>, vararg traces: String) {
        withContext(Dispatchers.IO) {
            innerMethod(deferred, *traces)
        }

        assertTrue(true)
    }

    private suspend fun innerMethod(deferred: Deferred<Nothing>, vararg traces: String) {
        try {
            deferred.await()
        } catch (e: RecoverableTestException) {
            verifyStackTrace(e, *traces)
        }
    }

    @Test
    fun testCoroutineScope() = runTest {
        val deferred = async(NonCancellable, start = CoroutineStart.LAZY) {
            throw RecoverableTestException()
        }

        outerScopedMethod(deferred,
            "kotlinx.coroutines.RecoverableTestException\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testCoroutineScope\$1\$deferred\$1.invokeSuspend(StackTraceRecoveryTest.kt:143)\n" +
                    "\t(Coroutine boundary)\n" +
                    "\tat kotlinx.coroutines.DeferredCoroutine.await\$suspendImpl(Builders.common.kt:99)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest.innerMethod(StackTraceRecoveryTest.kt:158)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$outerScopedMethod\$2.invokeSuspend(StackTraceRecoveryTest.kt:151)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testCoroutineScope\$1.invokeSuspend(StackTraceRecoveryTest.kt:141)\n",
            "Caused by: kotlinx.coroutines.RecoverableTestException\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testCoroutineScope\$1\$deferred\$1.invokeSuspend(StackTraceRecoveryTest.kt:143)\n" +
                    "\tat kotlin.coroutines.jvm.internal.BaseContinuationImpl.resumeWith(ContinuationImpl.kt:32)\n")
        deferred.join()
    }

    public class TrickyException() : Throwable() {
        // To be sure ctor is never invoked
        @Suppress("UNUSED", "UNUSED_PARAMETER")
        private constructor(message: String, cause: Throwable): this() {
            error("Should never be called")
        }

        override fun initCause(cause: Throwable?): Throwable {
            error("Can't call initCause")
        }
    }

    @Test
    fun testThrowingInitCause() = runTest {
        val deferred = async(NonCancellable) {
            expect(2)
            throw TrickyException()
        }

        try {
            expect(1)
            deferred.await()
        } catch (e: TrickyException) {
            assertNull(e.cause)
            finish(3)
        }
    }

    private suspend fun outerScopedMethod(deferred: Deferred<Nothing>, vararg traces: String) = coroutineScope {
        innerMethod(deferred, *traces)
        assertTrue(true)
    }

    @Test
    fun testSelect() = runTest {
        expect(1)
        val result = kotlin.runCatching { doSelect() }
        expect(3)
        verifyStackTrace(result.exceptionOrNull()!!,
            "kotlinx.coroutines.RecoverableTestException\n" +
                "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$doSelect\$\$inlined\$select\$lambda\$1.invokeSuspend(StackTraceRecoveryTest.kt:211)\n" +
                "\t(Coroutine boundary)\n" +
                "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testSelect\$1.invokeSuspend(StackTraceRecoveryTest.kt:199)\n" +
                "Caused by: kotlinx.coroutines.RecoverableTestException\n" +
                "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$doSelect\$\$inlined\$select\$lambda\$1.invokeSuspend(StackTraceRecoveryTest.kt:211)\n" +
                "\tat kotlin.coroutines.jvm.internal.BaseContinuationImpl.resumeWith(ContinuationImpl.kt:32)")
        finish(4)
    }

    private suspend fun doSelect(): Int {
        val job = CompletableDeferred(Unit)
        return select {
            job.onJoin {
                yield()
                expect(2)
                throw RecoverableTestException()
            }
        }
    }
}
