package kotlinx.coroutines

import kotlin.test.*

class CoroutinesJvmTest : TestBase() {
    @Test
    fun testNotCancellableCodeWithExceptionCancelled() = runTest(expected = {e -> e is TestException}) {
        expect(1)
        // CoroutineStart.ATOMIC makes sure it will not get cancelled for it starts executing
        val job = launch(start = CoroutineStart.ATOMIC) {
            Thread.sleep(100) // cannot be cancelled
            throwTestException() // will throw
            expectUnreached()
        }
        expect(2)
        job.cancel()
        finish(3)
    }

    @Test
    fun testCancelManyCompletedAttachedChildren() = runTest {
        val parent = launch { /* do nothing */ }
        val n = 10_000 * stressTestMultiplier
        repeat(n) {
            // create a child that already completed
            val child = launch(start = CoroutineStart.UNDISPATCHED) { /* do nothing */ }
            // attach it manually via internal API
            @Suppress("DEPRECATION_ERROR")
            parent.attachChild(child as ChildJob)
        }
        parent.cancelAndJoin() // cancel parent, make sure no stack overflow
    }

    private fun throwTestException(): Unit = throw TestException()
}