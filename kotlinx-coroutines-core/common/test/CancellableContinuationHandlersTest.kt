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
            // Nothing happened
            c.invokeOnCancellation { expectUnreached() }
            // Cannot validate after completion
            c.invokeOnCancellation { expectUnreached() }
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
