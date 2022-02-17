/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.guava

import kotlinx.coroutines.*
import org.junit.Test
import kotlin.test.*

class ListenableFutureToStringTest : TestBase() {
    @Test
    fun testSuccessfulFuture() = runTest {
        val deferred = CompletableDeferred("OK")
        val succeededFuture = deferred.asListenableFuture()
        val toString = succeededFuture.toString()
        assertTrue(message = "Unexpected format: $toString") {
            toString.matches(Regex("""kotlinx\.coroutines\.guava\.JobListenableFuture@[^\[]*\[status=SUCCESS, result=\[OK]]"""))
        }
    }

    @Test
    fun testFailedFuture() = runTest {
        val exception = TestRuntimeException("test")
        val deferred = CompletableDeferred<String>().apply {
            completeExceptionally(exception)
        }
        val failedFuture = deferred.asListenableFuture()
        val toString = failedFuture.toString()
        assertTrue(message = "Unexpected format: $toString") {
            toString.matches(Regex("""kotlinx\.coroutines\.guava\.JobListenableFuture@[^\[]*\[status=FAILURE, cause=\[$exception]]"""))
        }
    }

    @Test
    fun testPendingFuture() = runTest {
        val deferred = CompletableDeferred<String>()
        val pendingFuture = deferred.asListenableFuture()
        val toString = pendingFuture.toString()
        assertTrue(message = "Unexpected format: $toString") {
            toString.matches(Regex("""kotlinx\.coroutines\.guava\.JobListenableFuture@[^\[]*\[status=PENDING, delegate=\[.*]]"""))
        }
    }

    @Test
    fun testCancelledCoroutineAsListenableFuture() = runTest {
        val exception = CancellationException("test")
        val deferred = CompletableDeferred<String>().apply {
            cancel(exception)
        }
        val cancelledFuture = deferred.asListenableFuture()
        val toString = cancelledFuture.toString()
        assertTrue(message = "Unexpected format: $toString") {
            toString.matches(Regex("""kotlinx\.coroutines\.guava\.JobListenableFuture@[^\[]*\[status=CANCELLED, cause=\[$exception]]"""))
        }
    }

    @Test
    fun testCancelledFuture() = runTest {
        val deferred = CompletableDeferred<String>()
        val cancelledFuture = deferred.asListenableFuture().apply {
            cancel(false)
        }
        val toString = cancelledFuture.toString()
        assertTrue(message = "Unexpected format: $toString") {
            toString.matches(Regex("""kotlinx\.coroutines\.guava\.JobListenableFuture@[^\[]*\[status=CANCELLED]"""))
        }
    }
}
