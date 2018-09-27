/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines.experimental

import kotlinx.coroutines.experimental.channels.*
import kotlin.test.*

/**
 * Systematically tests that various builders cancel parent on failure.
 */
class ParentCancellationTest : TestBase() {
    @Test
    @Ignore // todo: shall be passing in Supervisor branch
    fun testJobChild() = runTest {
        testParentCancellation { fail ->
            val child = Job(coroutineContext[Job])
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
    fun testCoroutineScopeChild() = runTest {
        testParentCancellation(expectRethrows = true) { fail ->
            coroutineScope { fail() }
        }
    }

    @Test
    fun testWithContextChild() = runTest {
        testParentCancellation(expectRethrows = true) { fail ->
            withContext(CoroutineName("fail")) { fail() }
        }
    }

    @Test
    fun testWithTimeoutChild() = runTest {
        testParentCancellation(expectRethrows = true) { fail ->
            withTimeout(1000) { fail() }
        }
    }

    private suspend fun CoroutineScope.testParentCancellation(
        expectRethrows: Boolean = false,
        child: suspend CoroutineScope.(block: suspend CoroutineScope.() -> Unit) -> Unit
    ) {
        testWithException(expectRethrows, TestException(), child)
        testWithException(expectRethrows, CancellationException("Test"), child)
    }

    private suspend fun CoroutineScope.testWithException(
        expectRethrows: Boolean,
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
                val grandchild = launch {
                    throw throwException
                }
                grandchild.join()
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
        if (expectRethrows || throwException is CancellationException) {
            // Note: parent is not cancelled on CancellationException or when primitive rethrows it
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