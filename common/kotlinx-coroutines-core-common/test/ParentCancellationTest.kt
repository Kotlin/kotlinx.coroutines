/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines.experimental

import kotlinx.coroutines.experimental.channels.*
import kotlin.coroutines.experimental.*
import kotlin.test.*

/**
 * Systematically tests that various builders cancel parent on failure.
 */
class ParentCancellationTest : TestBase() {
    @Test
    fun testJobChild() = runTest {
        testParentCancellation(expectUnhandled = true) { fail ->
            val child = Job(coroutineContext[Job])
            CoroutineScope(coroutineContext + child).fail()
        }
    }

    @Test
    fun testSupervisorJobChild() = runTest {
        testParentCancellation(expectParentActive = true, expectUnhandled = true) { fail ->
            val child = SupervisorJob(coroutineContext[Job])
            CoroutineScope(coroutineContext + child).fail()
        }
    }

    @Test
    fun testCompletableDeferredChild() = runTest {
        testParentCancellation { fail ->
            val child = CompletableDeferred<Unit>(coroutineContext[Job])
            CoroutineScope(coroutineContext + child).fail()
        }
    }

    @Test
    fun testLaunchChild() = runTest {
        testParentCancellation { fail ->
            launch { fail() }
        }
    }

    @Test
    fun testAsyncChild() = runTest {
        testParentCancellation { fail ->
            async { fail() }
        }
    }

    @Test
    fun testProduceChild() = runTest {
        testParentCancellation { fail ->
            produce<Unit> { fail() }
        }
    }

    @Test
    fun testBroadcastChild() = runTest {
        testParentCancellation { fail ->
            broadcast<Unit> { fail() }.openSubscription()
        }
    }

    @Test
    fun testSupervisorChild() = runTest {
        testParentCancellation(expectParentActive = true, expectUnhandled = true) { fail ->
            supervisorScope { fail() }
        }
    }

    @Test
    fun testCoroutineScopeChild() = runTest {
        testParentCancellation(expectParentActive = true, expectRethrows = true) { fail ->
            coroutineScope { fail() }
        }
    }

    @Test
    fun testWithContextChild() = runTest {
        testParentCancellation(expectParentActive = true, expectRethrows = true) { fail ->
            withContext(CoroutineName("fail")) { fail() }
        }
    }

    @Test
    fun testWithTimeoutChild() = runTest {
        testParentCancellation(expectParentActive = true, expectRethrows = true) { fail ->
            withTimeout(1000) { fail() }
        }
    }

    private suspend fun CoroutineScope.testParentCancellation(
        expectParentActive: Boolean = false,
        expectRethrows: Boolean = false,
        expectUnhandled: Boolean = false,
        child: suspend CoroutineScope.(block: suspend CoroutineScope.() -> Unit) -> Unit
    ) {
        testWithException(expectParentActive, expectRethrows, expectUnhandled, TestException(), child)
        testWithException(true, expectRethrows, false, CancellationException("Test"), child)
    }

    private suspend fun CoroutineScope.testWithException(
        expectParentActive: Boolean,
        expectRethrows: Boolean,
        expectUnhandled: Boolean,
        throwException: Throwable,
        child: suspend CoroutineScope.(block: suspend CoroutineScope.() -> Unit) -> Unit
    ) {
        reset()
        expect(1)
        val parent = CompletableDeferred<Unit>() // parent that handles exception (!)
        val scope = CoroutineScope(coroutineContext + parent)
        try {
            scope.child {
                // launch failing grandchild
                var unhandledException: Throwable? = null
                val handler = CoroutineExceptionHandler { _, e -> unhandledException = e }
                val grandchild = launch(handler) {
                    throw throwException
                }
                grandchild.join()
                if (expectUnhandled) {
                    assertSame(throwException, unhandledException)
                } else {
                    assertNull(unhandledException)
                }
            }
            if (expectRethrows && throwException !is CancellationException) {
                expectUnreached()
            } else {
                expect(2)
            }
        } catch (e: Throwable) {
            if (expectRethrows) {
                expect(2)
                assertSame(throwException, e)
            } else {
                expectUnreached()
            }
        }
        if (expectParentActive) {
            assertTrue(parent.isActive)
        } else {
            parent.join()
            assertFalse(parent.isActive)
            assertTrue(parent.isCancelled)
        }
        finish(3)
    }

    private class TestException : Exception()
}