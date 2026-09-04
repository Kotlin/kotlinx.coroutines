package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import org.junit.Test
import kotlin.test.*

class DefaultExecutorStressTest : TestBase() {
    @Test
    fun testDelay() = runTest {
        val iterations = 100_000 * stressTestMultiplier
        withContext(DefaultDelay as CoroutineDispatcher) {
            expect(1)
            var expected = 1
            repeat(iterations) {
                expect(++expected)
                val deferred = async {
                    expect(++expected)
                    val largeArray = IntArray(10_000) { it }
                    delay(Long.MAX_VALUE)
                    println(largeArray) // consume to avoid DCE, actually unreachable
                }

                expect(++expected)
                yield()
                deferred.cancel()
                try {
                    deferred.await()
                } catch (e: CancellationException) {
                    expect(++expected)
                }
            }

        }
        finish(2 + iterations * 4)
    }
}
