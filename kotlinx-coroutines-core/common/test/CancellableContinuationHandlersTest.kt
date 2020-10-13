/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.test.*

class CancellableContinuationHandlersTest : TestBase() {

    @Test
    fun testDoubleSubscription() = runTest({ it is IllegalStateException }) {
        suspendCancellableCoroutine<Unit> { c ->
            c.invokeOnCancellation { finish(1) }
            c.invokeOnCancellation { expectUnreached() }
        }
    }

    @Test
    fun testDoubleSubscriptionAfterCompletion() = runTest {
        suspendCancellableCoroutine<Unit> { c ->
            c.resume(Unit)
            // First invokeOnCancellation is Ok
            c.invokeOnCancellation { expectUnreached() }
            // Second invokeOnCancellation is not allowed
            assertFailsWith<IllegalStateException> { c.invokeOnCancellation { expectUnreached() } }
        }
    }

    @Test
    fun testDoubleSubscriptionAfterCompletionWithException() = runTest {
        assertFailsWith<TestException> {
            suspendCancellableCoroutine<Unit> { c ->
                c.resumeWithException(TestException())
                // First invokeOnCancellation is Ok
                c.invokeOnCancellation { expectUnreached() }
                // Second invokeOnCancellation is not allowed
                assertFailsWith<IllegalStateException> { c.invokeOnCancellation { expectUnreached() } }
            }
        }
    }

    @Test
    fun testDoubleSubscriptionAfterCancellation() = runTest {
        try {
            suspendCancellableCoroutine<Unit> { c ->
                c.cancel()
                c.invokeOnCancellation {
                    assertTrue(it is CancellationException)
                    expect(1)
                }
                assertFailsWith<IllegalStateException> { c.invokeOnCancellation { expectUnreached() } }
            }
        } catch (e: CancellationException) {
            finish(2)
        }
    }

    @Test
    fun testSecondSubscriptionAfterCancellation() = runTest {
        try {
            suspendCancellableCoroutine<Unit> { c ->
                // Set IOC first
                c.invokeOnCancellation {
                    assertNull(it)
                    expect(2)
                }
                expect(1)
                // then cancel (it gets called)
                c.cancel()
                // then try to install another one
                assertFailsWith<IllegalStateException> { c.invokeOnCancellation { expectUnreached() } }
            }
        } catch (e: CancellationException) {
            finish(3)
        }
    }

    @Test
    fun testSecondSubscriptionAfterResumeCancelAndDispatch() = runTest {
        var cont: CancellableContinuation<Unit>? = null
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            // will be cancelled during dispatch
            assertFailsWith<CancellationException> {
                suspendCancellableCoroutine<Unit> { c ->
                    cont = c
                    // Set IOC first -- not called (completed)
                    c.invokeOnCancellation {
                        assertTrue(it is CancellationException)
                        expect(4)
                    }
                    expect(1)
                }
            }
            expect(5)
        }
        expect(2)
        // then resume it
        cont!!.resume(Unit) // schedule cancelled continuation for dispatch
        // then cancel the job during dispatch
        job.cancel()
        expect(3)
        yield() // finish dispatching (will call IOC handler here!)
        expect(6)
        // then try to install another one after we've done dispatching it
        assertFailsWith<IllegalStateException> {
            cont!!.invokeOnCancellation { expectUnreached() }
        }
        finish(7)
    }

    @Test
    fun testDoubleSubscriptionAfterCancellationWithCause() = runTest {
        try {
            suspendCancellableCoroutine<Unit> { c ->
                c.cancel(AssertionError())
                c.invokeOnCancellation {
                    require(it is AssertionError)
                    expect(1)
                }
                assertFailsWith<IllegalStateException> { c.invokeOnCancellation { expectUnreached() } }
            }
        } catch (e: AssertionError) {
            finish(2)
        }
    }

    @Test
    fun testDoubleSubscriptionMixed() = runTest {
        try {
            suspendCancellableCoroutine<Unit> { c ->
                c.invokeOnCancellation {
                    require(it is IndexOutOfBoundsException)
                    expect(1)
                }
                c.cancel(IndexOutOfBoundsException())
                assertFailsWith<IllegalStateException> { c.invokeOnCancellation { expectUnreached() } }
            }
        } catch (e: IndexOutOfBoundsException) {
            finish(2)
        }
    }

    @Test
    fun testExceptionInHandler() = runTest(
        unhandled = listOf({ it -> it is CompletionHandlerException })
    ) {
        expect(1)
        try {
            suspendCancellableCoroutine<Unit> { c ->
                c.invokeOnCancellation { throw AssertionError() }
                c.cancel()
            }
        } catch (e: CancellationException) {
            expect(2)
        }
        finish(3)
    }
}
