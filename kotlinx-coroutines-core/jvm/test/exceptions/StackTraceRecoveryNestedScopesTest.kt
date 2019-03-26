package kotlinx.coroutines.exceptions

import kotlinx.coroutines.*
import org.junit.*
import kotlin.coroutines.*

class StackTraceRecoveryNestedScopesTest : TestBase() {

    private val TEST_MACROS = "TEST_NAME"

    private val expectedTrace = "kotlinx.coroutines.RecoverableTestException\n" +
            "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedScopesTest.failure(StackTraceRecoveryNestedScopesTest.kt:9)\n" +
            "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedScopesTest.access\$failure(StackTraceRecoveryNestedScopesTest.kt:7)\n" +
            "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedScopesTest\$createFailingAsync\$1.invokeSuspend(StackTraceRecoveryNestedScopesTest.kt:12)\n" +
            "\t(Coroutine boundary)\n" +
            "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedScopesTest\$callWithTimeout\$2.invokeSuspend(StackTraceRecoveryNestedScopesTest.kt:23)\n" +
            "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedScopesTest\$callCoroutineScope\$2.invokeSuspend(StackTraceRecoveryNestedScopesTest.kt:29)\n" +
            "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedScopesTest\$$TEST_MACROS\$1.invokeSuspend(StackTraceRecoveryNestedScopesTest.kt:36)\n" +
            "Caused by: kotlinx.coroutines.RecoverableTestException\n" +
            "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedScopesTest.failure(StackTraceRecoveryNestedScopesTest.kt:9)\n" +
            "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedScopesTest.access\$failure(StackTraceRecoveryNestedScopesTest.kt:7)\n" +
            "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedScopesTest\$createFailingAsync\$1.invokeSuspend(StackTraceRecoveryNestedScopesTest.kt:12)\n" +
            "\tat kotlin.coroutines.jvm.internal.BaseContinuationImpl.resumeWith(ContinuationImpl.kt:32)"

    private fun failure(): String = throw RecoverableTestException()

    private fun CoroutineScope.createFailingAsync() = async {
        failure()
    }

    private suspend fun callWithContext(doYield: Boolean) = withContext(wrapperDispatcher(coroutineContext)) {
        if (doYield) yield()
        createFailingAsync().await()
        yield()
    }

    private suspend fun callWithTimeout(doYield: Boolean) = withTimeout(Long.MAX_VALUE) {
        if (doYield) yield()
        callWithContext(doYield)
        yield()
    }

    private suspend fun callCoroutineScope(doYield: Boolean) = coroutineScope {
        if (doYield) yield()
        callWithTimeout(doYield)
        yield()
    }

    @Test
    fun testNestedScopes() = runTest {
        try {
            callCoroutineScope(false)
        } catch (e: Exception) {
            verifyStackTrace(e, expectedTrace.replace(TEST_MACROS, "testNestedScopes"))
        }
    }

    @Test
    fun testNestedScopesYield() = runTest {
        try {
            callCoroutineScope(true)
        } catch (e: Exception) {
            verifyStackTrace(e, expectedTrace.replace(TEST_MACROS, "testNestedScopesYield"))
        }
    }

    @Test
    fun testAwaitNestedScopes() = runTest {
        val deferred = async(NonCancellable) {
            callCoroutineScope(false)
        }

        verifyAwait(deferred)
    }

    private suspend fun verifyAwait(deferred: Deferred<Unit>) {
        try {
            deferred.await()
        } catch (e: Exception) {
            verifyStackTrace(e,
                "kotlinx.coroutines.RecoverableTestException\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedScopesTest.failure(StackTraceRecoveryNestedScopesTest.kt:23)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedScopesTest.access\$failure(StackTraceRecoveryNestedScopesTest.kt:7)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedScopesTest\$createFailingAsync\$1.invokeSuspend(StackTraceRecoveryNestedScopesTest.kt:26)\n" +
                    "\t(Coroutine boundary)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedScopesTest\$callWithTimeout\$2.invokeSuspend(StackTraceRecoveryNestedScopesTest.kt:37)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedScopesTest\$callCoroutineScope\$2.invokeSuspend(StackTraceRecoveryNestedScopesTest.kt:43)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedScopesTest\$testAwaitNestedScopes\$1\$deferred\$1.invokeSuspend(StackTraceRecoveryNestedScopesTest.kt:68)\n" +
                    "\tat kotlinx.coroutines.DeferredCoroutine.await\$suspendImpl(Builders.common.kt:99)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedScopesTest.verifyAwait(StackTraceRecoveryNestedScopesTest.kt:76)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedScopesTest\$testAwaitNestedScopes\$1.invokeSuspend(StackTraceRecoveryNestedScopesTest.kt:71)\n" +
                "Caused by: kotlinx.coroutines.RecoverableTestException\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedScopesTest.failure(StackTraceRecoveryNestedScopesTest.kt:23)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedScopesTest.access\$failure(StackTraceRecoveryNestedScopesTest.kt:7)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedScopesTest\$createFailingAsync\$1.invokeSuspend(StackTraceRecoveryNestedScopesTest.kt:26)\n" +
                    "\tat kotlin.coroutines.jvm.internal.BaseContinuationImpl.resumeWith(ContinuationImpl.kt:32)")
        }
    }
}
