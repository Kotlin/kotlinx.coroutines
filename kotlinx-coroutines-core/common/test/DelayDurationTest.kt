/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED", "DEPRECATION")

// KT-21913

package kotlinx.coroutines

import kotlin.test.*
import kotlin.time.*

@ExperimentalTime
class DelayDurationTest : TestBase() {

    @Test
    fun testCancellation() = runTest(expected = { it is CancellationException }) {
        runAndCancel(1.seconds)
    }

    @Test
    fun testInfinite() = runTest(expected = { it is CancellationException }) {
        runAndCancel(Duration.INFINITE)
    }

    @Test
    fun testRegularDelay() = runTest {
        val deferred = async {
            expect(2)
            delay(1.seconds)
            expect(4)
        }

        expect(1)
        yield()
        expect(3)
        deferred.await()
        finish(5)
    }

    @Test
    fun testNanoDelay() = runTest {
        val deferred = async {
            expect(2)
            delay(1.nanoseconds)
            expect(4)
        }

        expect(1)
        yield()
        expect(3)
        deferred.await()
        finish(5)
    }

    private suspend fun runAndCancel(time: Duration) = coroutineScope {
        expect(1)
        val deferred = async {
            expect(2)
            delay(time)
            expectUnreached()
        }

        yield()
        expect(3)
        require(deferred.isActive)
        deferred.cancel()
        finish(4)
        deferred.await()
    }
}
