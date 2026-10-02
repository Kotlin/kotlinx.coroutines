package kotlinx.coroutines.jdk9

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlin.test.*
import java.util.concurrent.Flow as JFlow

class AwaitTest: TestBase() {

    /** Tests that calls to [awaitFirst] (and, thus, to the rest of these functions) throw [CancellationException] and
     * unsubscribe from the publisher when their [Job] is cancelled. */
    @Test
    fun testAwaitCancellation() = runTest {
        expect(1)
        val publisher = JFlow.Publisher<Int> { s ->
            s.onSubscribe(object : JFlow.Subscription {
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
