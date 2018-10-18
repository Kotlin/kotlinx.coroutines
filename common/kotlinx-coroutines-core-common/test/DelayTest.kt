
/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED", "DEPRECATION") // KT-21913

package kotlinx.coroutines

import kotlin.test.*

class DelayTest : TestBase() {

    @Test
    fun testCancellation() = runTest(expected = {it is CancellationException }) {
        runAndCancel(1000)
    }

    @Test
    fun testMaxLongValue()= runTest(expected = {it is CancellationException }) {
        runAndCancel(Long.MAX_VALUE)
    }

    @Test
    fun testMaxIntValue()= runTest(expected = {it is CancellationException }) {
        runAndCancel(Int.MAX_VALUE.toLong())
    }

    @Test
    fun testRegularDelay() = runTest {
        val deferred = async {
            expect(2)
            delay(1)
            expect(3)
        }

        expect(1)
        yield()
        deferred.await()
        finish(4)
    }

    private suspend fun runAndCancel(time: Long) = coroutineScope {
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
