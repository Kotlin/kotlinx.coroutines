package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.test.*

/** See #1061. [kotlinx.coroutines.flow.SharingReferenceTest] was used as inspiration. */
class NonCancellableScopeReferenceTest: TestBase() {
    private val token = object {}

    /** Tests that the calling coroutine keeps a strong reference on the coroutine in [nonCancellable]. */
    @Test
    fun testNonCancellableReference() {
        /** Need to create a new executor and a coroutine scope (can't use [runTest]),
         * as we want to obtain an object graph completely separate from the running test body.
         * Otherwise, [token] could leak through them, making this test inconclusive. */
        newSingleThreadContext("NonCancellable").use { ctx ->
            val coroutine = CoroutineScope(ctx).async(start = CoroutineStart.UNDISPATCHED) {
                nonCancellable {
                    suspendCancellableCoroutine<Unit> {}
                    token
                }
            }
            FieldWalker.assertReachableCount(1, coroutine) { it === token }
        }
    }

    /** Tests that the strong reference the calling coroutine keeps on [nonCancellable] gets properly removed. */
    @Test
    fun testNonCancellableNoMemoryLeak() = runTest {
        suspend fun runSomeTasks() {
            repeat(10) {
                nonCancellable { }
            }
        }
        // Warm-up: converge to a consistent state of the coroutine job. `10` is arbitrary.
        runSomeTasks()
        val items = FieldWalker.walk(currentCoroutineContext())
        runSomeTasks()
        val items2 = FieldWalker.walk(currentCoroutineContext())
        assertTrue(items2.size <= items.size)

    }
}
