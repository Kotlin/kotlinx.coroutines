package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import org.junit.*

class AwaitJvmTest : TestBase() {
    @Test
    public fun testSecondLeak() = runTest {
        // This test is to make sure that handlers installed on the second deferred do not leak
        val d1 = CompletableDeferred<Int>()
        val d2 = CompletableDeferred<Int>()
        d1.completeExceptionally(TestException()) // first is crashed
        val iterations = 3_000_000 * stressTestMultiplier
        for (iter in 1..iterations) {
            try {
                awaitAll(d1, d2)
                expectUnreached()
            } catch (e: TestException) {
                expect(iter)
            }
        }
        finish(iterations + 1)
    }
}