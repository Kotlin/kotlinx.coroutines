/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug.junit5

import kotlinx.coroutines.*
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.extension.*
import org.junit.jupiter.api.parallel.*

class CoroutinesTimeoutExtensionTest {

    /**
     * Tests that disabling coroutine creation stacktraces in [CoroutinesTimeoutExtension] does lead to them not being
     * created.
     *
     * Adapted from [CoroutinesTimeoutDisabledTracesTest], an identical test for the JUnit4 rule.
     *
     * This test class is not intended to be run manually. Instead, use [CoroutinesTimeoutTest] as the entry point.
     */
    class DisabledStackTracesTest {
        @JvmField
        @RegisterExtension
        internal val timeout = CoroutinesTimeoutExtension(500, true, false)

        private val job = GlobalScope.launch(Dispatchers.Unconfined) { hangForever() }

        private suspend fun hangForever() {
            suspendCancellableCoroutine<Unit> {  }
            expectUnreached()
        }

        @Test
        fun hangingTest() = runBlocking<Unit> {
            waitForHangJob()
            expectUnreached()
        }

        private suspend fun waitForHangJob() {
            job.join()
            expectUnreached()
        }
    }

    /**
     * Tests that [CoroutinesTimeoutExtension] is installed eagerly and detects the coroutines that were launched before
     * any test events start happening.
     *
     * Adapted from [CoroutinesTimeoutEagerTest], an identical test for the JUnit4 rule.
     *
     * This test class is not intended to be run manually. Instead, use [CoroutinesTimeoutTest] as the entry point.
     */
    class EagerTest {

        @JvmField
        @RegisterExtension
        internal val timeout = CoroutinesTimeoutExtension(500)

        private val job = GlobalScope.launch(Dispatchers.Unconfined) { hangForever() }

        private suspend fun hangForever() {
            suspendCancellableCoroutine<Unit> {  }
            expectUnreached()
        }

        @Test
        fun hangingTest() = runBlocking<Unit> {
            waitForHangJob()
            expectUnreached()
        }

        private suspend fun waitForHangJob() {
            job.join()
            expectUnreached()
        }
    }

    /**
     * Tests that [CoroutinesTimeoutExtension] performs sensibly in some simple scenarios.
     *
     * Adapted from [CoroutinesTimeoutTest], an identical test for the JUnit4 rule.
     *
     * This test class is not intended to be run manually. Instead, use [CoroutinesTimeoutTest] as the entry point.
     */
    class SimpleTest {

        @JvmField
        @RegisterExtension
        internal val timeout = CoroutinesTimeoutExtension(1000, false, true)

        @Test
        fun hangingTest() = runBlocking<Unit> {
            suspendForever()
            expectUnreached()
        }

        private suspend fun suspendForever() {
            delay(Long.MAX_VALUE)
            expectUnreached()
        }

        @Test
        fun throwingTest() = runBlocking<Unit> {
            throw RuntimeException()
        }

        @Test
        fun successfulTest() = runBlocking {
            val job = launch {
                yield()
            }

            job.join()
        }
    }
}

private fun expectUnreached(): Nothing {
    error("Should not be reached")
}