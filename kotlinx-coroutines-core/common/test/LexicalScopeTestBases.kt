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

    /** Tests that [scopeFunctionUnderTest] cancels its children when it fails. */
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
abstract class DecomposingLexicalScopeTestBase: TestBase() {
    abstract suspend fun <T> scopeFunctionUnderTest(block: suspend CoroutineScope.() -> T): T

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
}
