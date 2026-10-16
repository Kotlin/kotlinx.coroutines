package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import kotlin.test.*

class SafeCollectorMutatingContextStressTest: TestBase() {
    /** Regression test for #4774 */
    @Test
    fun testAccessingSafeCollectorBySuspendingInTailPosition() = runTest {
        repeat(1000 * stressTestMultiplier) {
            val channel = Channel<Int>(capacity = 0)
            val source = flow {
                // Emissions from inside the collection of a buffered flow,
                // i.e. from the coroutineScope of ChannelFlow.collect()
                flowOf(1, 2, 3).buffer(Channel.RENDEZVOUS).collect { emit(it) }
                // Emissions from outside of it, once that scope has completed
                emit(4)
                emit(5)
            }

            coroutineScope {
                launch(Dispatchers.Default) {
                    try {
                        // send() is a tail call: it suspends on the SafeCollector of `source`
                        source.collect { channel.send(it) }
                        channel.close()
                    } catch (e: Throwable) {
                        // Without this, the JobCancellationException is handled as a normal
                        // cancellation of the launch, and the consumer below waits forever
                        channel.close(e)
                        throw e
                    }
                }
                // Consume on another thread
                channel.consumeEach { }
            }
        }
    }
}
