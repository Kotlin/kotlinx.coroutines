/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.exceptions

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.intrinsics.*
import org.junit.Test
import java.lang.RuntimeException
import java.util.concurrent.*
import kotlin.concurrent.*
import kotlin.coroutines.*
import kotlin.test.*

/*
 * All stacktrace validation skips line numbers
 */
class StackTraceRecoveryTest : TestBase() {

    @Test
    fun testAsync() = runTest {
        fun createDeferred(depth: Int): Deferred<*> {
            return if (depth == 0) {
                async<Unit>(coroutineContext + NonCancellable) {
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
                    "\tat _COROUTINE._BOUNDARY._(CoroutineDebugging.kt)\n" +
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
        val deferred = async<Unit>(coroutineContext + NonCancellable) {
            throw ExecutionException(null)
        }

        deferred.join()
        val stacktrace = listOf(
            "java.util.concurrent.ExecutionException\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testCompletedAsync\$1\$deferred\$1.invokeSuspend(StackTraceRecoveryTest.kt:44)\n" +
                    "\tat _COROUTINE._BOUNDARY._(CoroutineDebugging.kt)\n" +
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
    fun testWithContext() = runTest {
        val deferred = async<Unit>(NonCancellable, start = CoroutineStart.LAZY) {
            throw RecoverableTestException()
        }

        outerMethod(deferred,
            "kotlinx.coroutines.RecoverableTestException\n" +
                "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testWithContext\$1\$deferred\$1.invokeSuspend(StackTraceRecoveryTest.kt:143)\n" +
                "\tat _COROUTINE._BOUNDARY._(CoroutineDebugging.kt)\n" +
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

    private suspend fun outerMethod(deferred: Deferred<*>, vararg traces: String) {
        withContext(Dispatchers.IO) {
            innerMethod(deferred, *traces)
        }

        assertTrue(true)
    }

    private suspend fun innerMethod(deferred: Deferred<*>, vararg traces: String) {
        try {
            deferred.await()
            expectUnreached()
        } catch (e: RecoverableTestException) {
            verifyStackTrace(e, *traces)
        }
    }

    @Test
    fun testCoroutineScope() = runTest {
        val deferred = async<Unit>(NonCancellable, start = CoroutineStart.LAZY) {
            throw RecoverableTestException()
        }

        outerScopedMethod(deferred,
            "kotlinx.coroutines.RecoverableTestException\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testCoroutineScope\$1\$deferred\$1.invokeSuspend(StackTraceRecoveryTest.kt:143)\n" +
                    "\tat _COROUTINE._BOUNDARY._(CoroutineDebugging.kt)\n" +
                    "\tat kotlinx.coroutines.DeferredCoroutine.await\$suspendImpl(Builders.common.kt:99)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest.innerMethod(StackTraceRecoveryTest.kt:158)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$outerScopedMethod\$2\$1.invokeSuspend(StackTraceRecoveryTest.kt:193)\n" +
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
        val deferred = async<Unit>(NonCancellable) {
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

    private suspend fun outerScopedMethod(deferred: Deferred<*>, vararg traces: String) = coroutineScope {
        supervisorScope {
            innerMethod(deferred, *traces)
            assertTrue(true)
        }
        assertTrue(true)
    }

    @Test
    fun testSelfSuppression() = runTest {
        try {
            runBlocking {
                val job = launch {
                    coroutineScope<Unit> {
                        throw RecoverableTestException()
                    }
                }

                job.join()
                expectUnreached()
            }
            expectUnreached()
        } catch (e: RecoverableTestException) {
            checkCycles(e)
        }
    }


    private suspend fun throws() {
        yield() // TCE
        throw RecoverableTestException()
    }

    private suspend fun awaiter() {
        val task = GlobalScope.async(Dispatchers.Default, start = CoroutineStart.LAZY) { throws() }
        task.await()
        yield() // TCE
    }

    @Test
    fun testNonDispatchedRecovery() {
        val await = suspend { awaiter() }

        val barrier = CyclicBarrier(2)
        var exception: Throwable? = null

        thread {
            await.startCoroutineUnintercepted(Continuation(EmptyCoroutineContext) {
                exception = it.exceptionOrNull()
                barrier.await()
            })
        }

        barrier.await()
        val e = exception
        assertNotNull(e)
        verifyStackTrace(e, "kotlinx.coroutines.RecoverableTestException\n" +
                "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest.throws(StackTraceRecoveryTest.kt:280)\n" +
                "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$throws\$1.invokeSuspend(StackTraceRecoveryTest.kt)\n" +
                "\tat _COROUTINE._BOUNDARY._(CoroutineDebugging.kt)\n" +
                "\tat kotlinx.coroutines.DeferredCoroutine.await\$suspendImpl(Builders.common.kt:99)\n" +
                "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest.awaiter(StackTraceRecoveryTest.kt:285)\n" +
                "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testNonDispatchedRecovery\$await\$1.invokeSuspend(StackTraceRecoveryTest.kt:291)\n" +
                "Caused by: kotlinx.coroutines.RecoverableTestException")
    }

    private class Callback(val cont: CancellableContinuation<*>)

    @Test
    fun testCancellableContinuation() = runTest {
        val channel = Channel<Callback>(1)
        launch {
            try {
                awaitCallback(channel)
            } catch (e: Throwable) {
                verifyStackTrace(e, "kotlinx.coroutines.RecoverableTestException\n" +
                        "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testCancellableContinuation\$1.invokeSuspend(StackTraceRecoveryTest.kt:329)\n" +
                        "\tat _COROUTINE._BOUNDARY._(CoroutineDebugging.kt)\n" +
                        "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest.awaitCallback(StackTraceRecoveryTest.kt:348)\n" +
                        "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testCancellableContinuation\$1\$1.invokeSuspend(StackTraceRecoveryTest.kt:322)\n" +
                        "Caused by: kotlinx.coroutines.RecoverableTestException\n" +
                        "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryTest\$testCancellableContinuation\$1.invokeSuspend(StackTraceRecoveryTest.kt:329)")
            }
        }
        val callback = channel.receive()
        callback.cont.resumeWithException(RecoverableTestException())
    }

    private suspend fun awaitCallback(channel: Channel<Callback>) {
        suspendCancellableCoroutine<Unit> { cont ->
            channel.offer(Callback(cont))
        }
        yield() // nop to make sure it is not a tail call
    }

    @Test
    fun testWrongMessageException() = runTest {
        val result = runCatching {
            coroutineScope<Unit> {
                throw WrongMessageException("OK")
            }
        }
        val ex = result.exceptionOrNull() ?: error("Expected to fail")
        assertTrue(ex is WrongMessageException)
        assertEquals("Token OK", ex.message)
    }

    public class WrongMessageException(token: String) : RuntimeException("Token $token")
}
