/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.exceptions

import kotlinx.coroutines.*
import kotlinx.coroutines.time.*
import org.junit.*
import org.junit.rules.*

class StackTraceRecoveryWithTimeoutTest : TestBase() {

    @get:Rule
    val name = TestName()

    @Test
    fun testStacktraceIsRecoveredFromSuspensionPoint() = runTest {
        try {
            outerWithTimeout()
        } catch (e: TimeoutException) {
            verifyStackTrace("timeout/${name.methodName}", e)
        }
    }

    private suspend fun outerWithTimeout() {
        kotlinx.coroutines.time.withTimeout(200) {
            suspendForever()
        }
        expectUnreached()
    }

    private suspend fun suspendForever() {
        hang { }
        expectUnreached()
    }

    @Test
    fun testStacktraceIsRecoveredFromLexicalBlockWhenTriggeredByChild() = runTest {
        try {
            outerChildWithTimeout()
        } catch (e: TimeoutException) {
            verifyStackTrace("timeout/${name.methodName}", e)
        }
    }

    private suspend fun outerChildWithTimeout() {
        kotlinx.coroutines.time.withTimeout(200) {
            launch {
                withTimeoutInChild()
            }
            yield()
        }
        expectUnreached()
    }

    private suspend fun withTimeoutInChild() {
        kotlinx.coroutines.time.withTimeout(300) {
            hang { }
        }
        expectUnreached()
    }

    @Test
    fun testStacktraceIsRecoveredFromSuspensionPointWithChild() = runTest {
        try {
            outerChild()
        } catch (e: TimeoutException) {
            verifyStackTrace("timeout/${name.methodName}", e)
        }
    }

    private suspend fun outerChild() {
        kotlinx.coroutines.time.withTimeout(200) {
            launch {
                smallWithTimeout()
            }
            suspendForever()
        }
        expectUnreached()
    }

    private suspend fun smallWithTimeout() {
        kotlinx.coroutines.time.withTimeout(100) {
            suspendForever()
        }
        expectUnreached()
    }
}
