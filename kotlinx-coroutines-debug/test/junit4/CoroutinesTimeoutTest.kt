/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug.junit4

import kotlinx.coroutines.*
import org.junit.*
import org.junit.runners.model.*

class CoroutinesTimeoutTest : TestBase() {

    @Rule
    @JvmField
    public val validation = TestFailureValidation(
        1000, false, true,
        TestResultSpec("throwingTest", error = RuntimeException::class.java),
        TestResultSpec("successfulTest"),
        TestResultSpec(
            "hangingTest", expectedOutParts = listOf(
                "Coroutines dump",
                "Test hangingTest timed out after 1 seconds",
                "BlockingCoroutine{Active}",
                "runBlocking",
                "at kotlinx.coroutines.debug.junit4.CoroutinesTimeoutTest.suspendForever",
                "at kotlinx.coroutines.debug.junit4.CoroutinesTimeoutTest\$hangingTest\$1.invokeSuspend"),
            notExpectedOutParts = listOf("delay", "throwingTest"),
            error = TestTimedOutException::class.java)
    )

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
