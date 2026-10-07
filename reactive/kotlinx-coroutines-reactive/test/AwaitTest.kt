package kotlinx.coroutines.reactive

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import org.reactivestreams.*
import kotlin.test.*

class AwaitTest: TestBase() {

    /** Tests that calls to [awaitFirst] (and, thus, to the rest of these functions) throw [CancellationException] and
     * unsubscribe from the publisher when their [Job] is cancelled. */
    @Test
    fun testAwaitCancellation() = runTest {
        expect(1)
        val publisher = Publisher<Int> { s ->
            s.onSubscribe(object: Subscription {
                override fun request(n: Long) {
                    expect(3)
                }

                override fun cancel() {
                    expect(5)
                }
            })
        }
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            assertFailsWith<CancellationException> {
                publisher.awaitFirst()
            }
            expect(6)
        }
        expect(4)
        job.cancelAndJoin()
        finish(7)
    }

}
