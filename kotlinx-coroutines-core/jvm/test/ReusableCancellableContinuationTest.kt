/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.channels.*
import org.junit.Test
import kotlin.coroutines.*
import kotlin.test.*

class ReusableCancellableContinuationTest : TestBase() {

    @Test
    fun testReusable() = runTest {
        testContinuationsCount(10, 1, ::suspendAtomicCancellableCoroutineReusable)
    }

    @Test
    fun testRegular() = runTest {
        testContinuationsCount(10, 10, ::suspendAtomicCancellableCoroutine)
    }

    private suspend inline fun CoroutineScope.testContinuationsCount(
        iterations: Int,
        expectedInstances: Int,
        suspender: suspend ((CancellableContinuation<Unit>) -> Unit) -> Unit
    ) {
        val result = mutableSetOf<CancellableContinuation<*>>()
        val job = coroutineContext[Job]!!
        val channel = Channel<Continuation<Unit>>(1)
        launch {
            channel.consumeEach {
                val f = FieldWalker.walk(job)
                result.addAll(f.filterIsInstance<CancellableContinuation<*>>())
                it.resumeWith(Result.success(Unit))
            }
        }

        repeat(iterations) {
            suspender {
                assertTrue(channel.offer(it))
            }
        }
        channel.close()
        assertEquals(expectedInstances, result.size - 1)
    }

    @Test
    fun testCancelledOnClaimedCancel() = runTest {
        expect(1)
        try {
            suspendAtomicCancellableCoroutineReusable<Unit> {
                it.cancel()
            }
            expectUnreached()
        } catch (e: CancellationException) {
            finish(2)
        }
    }

    @Test
    fun testNotCancelledOnClaimedResume() = runTest {
        expect(1)
        suspendAtomicCancellableCoroutineReusable<Unit> {
            it.cancel()
            it.resume(Unit)
        }
        ensureActive()
        finish(2)
    }

    @Test
    fun testResumeReusablePreservesReference() = runTest {
        expect(1)
        var cont: Continuation<Unit>? = null
        launch {
            cont!!.resumeWith(Result.success(Unit))
        }
        suspendAtomicCancellableCoroutineReusable<Unit> {
            cont = it
        }
        ensureActive()
        assertTrue { FieldWalker.walk(coroutineContext[Job]!!).contains(cont!!) }
        finish(2)
    }

    @Test
    fun testResumeRegularDoesntPreservesReference() = runTest {
        expect(1)
        var cont: Continuation<Unit>? = null
        launch {
            cont!!.resumeWith(Result.success(Unit))
        }
        suspendAtomicCancellableCoroutine<Unit> {
            cont = it
        }
        ensureActive()
        assertFalse { FieldWalker.walk(coroutineContext[Job]!!).contains(cont!!) }
        finish(2)
    }

    @Test
    fun testDetachedOnCancel() = runTest {
        expect(1)
        var cont: Continuation<*>? = null
        try {
            suspendAtomicCancellableCoroutineReusable<Unit> {
                cont = it
                it.cancel()
            }
            expectUnreached()
        } catch (e: CancellationException) {
            assertFalse { FieldWalker.walk(coroutineContext[Job]!!).contains(cont!!) }
            finish(2)
        }
    }
}
