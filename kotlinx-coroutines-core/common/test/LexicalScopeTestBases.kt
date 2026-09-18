@file:OptIn(ExperimentalAtomicApi::class)
package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.concurrent.atomics.*
import kotlin.test.*

/** Base class for lexical coroutine scopes. */
abstract class LexicalScopeTestBase: TestBase() {
    abstract suspend fun <T> scopeFunctionUnderTest(block: suspend CoroutineScope.() -> T): T

    /** Tests that [scopeFunctionUnderTest] waits for its children to complete before returning. */
    @Test
    fun testScopeAwaitingChildrenOnSuccess() = runTest {
        val latch = Job()
        var parentScopeExited = false
        this@runTest.launch {
            repeat(100) { yield() } // spinning until quiescence
            assertFalse(parentScopeExited)
            latch.complete()
        }
        val children = scopeFunctionUnderTest {
            List(5) {
                launch {
                    latch.join()
                }
            }
        }
        parentScopeExited = true
        children.forEach {
            assertTrue(it.isCompleted)
        }
    }

    /** Tests that [scopeFunctionUnderTest] cancels the children that arrive after its completion. */
    @Test
    fun testScopeCancellingExternallySubmittedChildren() = runTest {
        val scope = scopeFunctionUnderTest {
            this // leaking the `CoroutineScope`
        }
        assertFalse(scope.isActive)
        val newChild = scope.launch {
            this@runTest.cancel(CancellationException("Test failure: the child should not run"))
        }
        assertFalse(newChild.isActive)
        assertTrue(newChild.isCancelled)
    }

    /** Tests that [scopeFunctionUnderTest] does not cancel the caller coroutine when it fails. */
    @Test
    fun testScopeFailureNotCancellingParent() = runTest {
        assertFailsWith<TestException> {
            scopeFunctionUnderTest {
                throw TestException()
            }
        }
        assertTrue(isActive)
    }

    /** Tests that [scopeFunctionUnderTest] cancels its children and rethrows the failure exception when it fails. */
    @Test
    fun testScopeFailureCancellingChildren() = runTest {
        val nChildren = 5
        val childrenCompleted = AtomicInt(0)
        assertFailsWith<TestException> {
            scopeFunctionUnderTest {
                repeat(nChildren) {
                    launch(start = CoroutineStart.UNDISPATCHED) {
                        try {
                            awaitCancellation()
                        } finally {
                            childrenCompleted.fetchAndIncrement()
                        }
                    }
                }
                throw TestException()
            }
        }
        assertTrue(isActive)
        assertEquals(nChildren, childrenCompleted.load())
    }
}

/** Base class for testing lexical coroutine scopes whose children cancel the parent on their own failure. */
abstract class DecomposingLexicalScopeTestBase: LexicalScopeTestBase() {

    /** Tests that [scopeFunctionUnderTest] gets cancelled on child failure. */
    @Test
    fun testScopeFailingOnChildFailure() = runTest {
        expect(1)
        assertFailsWith<TestException> {
            scopeFunctionUnderTest {
                // Launching a child that should get cancelled
                launch(start = CoroutineStart.UNDISPATCHED) {
                    try {
                        awaitCancellation()
                    } finally {
                        expect(3)
                    }
                }
                // Launching a child that will fail
                launch {
                    expect(2)
                    throw TestException()
                }
            }
        }
        finish(4)
    }

    /** Tests that the first failure in either [scopeFunctionUnderTest] or its children gets reported,
     * and the other failures are suppressed. */
    @Test
    fun testScopeFailuresChronologicalOrder() = runTest {
        val nChildren = 4
        repeat(nChildren + 1) { firstToGo ->
            val boxOfContinuations = MutableList<CancellableContinuation<Nothing>?>(nChildren + 1) { null }
            val canStartCancelling = Job()
            launch {
                canStartCancelling.join()
                boxOfContinuations[firstToGo]!!.resumeWith(Result.failure(TestException("$firstToGo")))
            }
            assertFailsWith<TestException> {
                scopeFunctionUnderTest {
                    repeat(nChildren) {
                        launch(start = CoroutineStart.UNDISPATCHED) {
                            try {
                                suspendCancellableCoroutine { cont ->
                                    boxOfContinuations[it] = cont
                                }
                            } catch (_: CancellationException) {
                                throw TestException2("$it")
                            }
                        }
                    }
                    try {
                        suspendCancellableCoroutine { cont ->
                            boxOfContinuations[nChildren] = cont
                            canStartCancelling.complete()
                        }
                    } catch (_: CancellationException) {
                        throw TestException2("$nChildren")
                    }
                }
            }.apply {
                assertEquals("$firstToGo", message)
                assertEquals(nChildren, suppressedExceptions.size)
                assertTrue(suppressedExceptions.all { it is TestException2 })
                // Make sure no exception got counted twice
                assertEquals(
                    List(nChildren + 1) { "$it" }.toSet(),
                    suppressedExceptions.map { it.message }.toSet() + message
                )
            }
        }
    }
}
