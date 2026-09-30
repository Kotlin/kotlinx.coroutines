package kotlinx.coroutines.exceptions

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import org.junit.*
import org.junit.rules.*
import kotlin.time.Duration.Companion.milliseconds

class StackTraceRecoveryWithTimeoutTest : TestBase() {

    @get:Rule
    val name = TestName()

    @Test
    fun testStacktraceIsRecoveredFromSuspensionPoint() = runTest {
        try {
            outerWithTimeout()
        } catch (e: TimeoutCancellationException) {
            verifyStackTrace("timeout/${name.methodName}", e)
        }
    }

    private suspend fun outerWithTimeout() {
        withTimeout(200.milliseconds) {
            suspendForever()
        }
        expectUnreached()
    }

    private suspend fun suspendForever() {
        hang {  }
        expectUnreached()
    }

    @Test
    fun testStacktraceIsRecoveredFromLexicalBlockWhenTriggeredByChild() = runTest {
        try {
            outerChildWithTimeout()
        } catch (e: TimeoutCancellationException) {
            verifyStackTrace("timeout/${name.methodName}", e)
        }
    }

    private suspend fun outerChildWithTimeout() {
        withTimeout(200.milliseconds) {
            launch {
                withTimeoutInChild()
            }
            yield()
        }
        expectUnreached()
    }

    private suspend fun withTimeoutInChild() {
        withTimeout(300.milliseconds) {
            hang {  }
        }
        expectUnreached()
    }

    @Test
    fun testStacktraceIsRecoveredFromSuspensionPointWithChild() = runTest {
        try {
            outerChild()
        } catch (e: TimeoutCancellationException) {
            verifyStackTrace("timeout/${name.methodName}", e)
        }
    }

    private suspend fun outerChild() {
        withTimeout(200.milliseconds) {
            launch {
                smallWithTimeout()
            }
            suspendForever()
        }
        expectUnreached()
    }

    private suspend fun smallWithTimeout() {
        withTimeout(100.milliseconds) {
            suspendForever()
        }
        expectUnreached()
    }
}
