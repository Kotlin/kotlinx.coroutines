package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.test.*

@Suppress("DEPRECATION")
class NonCancellableScopeTest : TestBase() {
    /** Tests that [nonCancellable] does not react to the caller coroutine having been cancelled. */
    @Test
    fun testNonCancellableScopeDoesNotReactToCancellation() = runTest {
        expect(1)
        launch {
            this@launch.cancel()
            nonCancellable {
                yield()
                expect(2)
            }
            finish(3)
        }
    }

    /** Tests that [nonCancellable] does not react to the caller coroutine having failed. */
    @Test
    fun testNonCancellableScopeDoesNotReactToFailure() = runTest {
        expect(1)
        supervisorScope {
            /** Starting a separate [async] coroutine in a [supervisorScope] to prevent error propagation */
            val deferred = async {
                launch(start = CoroutineStart.UNDISPATCHED) {
                    throw TestException("Failure")
                }
                expect(2)
                assertFalse(isActive)
                nonCancellable {
                    yield()
                    expect(3)
                }
                finish(4)
            }
            assertFailsWith<TestException> { deferred.await() }
        }
    }


    class NonCancellableIsLexicalScope: LexicalScopeTestBase() {
        override suspend fun <T> scopeFunctionUnderTest(block: suspend CoroutineScope.() -> T): T =
            nonCancellable(block)
    }

    class NonCancellableIsDecomposingLexicalScope: DecomposingLexicalScopeTestBase() {
        override suspend fun <T> scopeFunctionUnderTest(block: suspend CoroutineScope.() -> T): T =
            nonCancellable(block)
    }
}
