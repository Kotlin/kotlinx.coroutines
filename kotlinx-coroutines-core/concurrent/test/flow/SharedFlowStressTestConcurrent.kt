package kotlinx.coroutines

import kotlinx.coroutines.flow.MutableSharedFlow
import kotlinx.coroutines.testing.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

class SharedFlowStressTestConcurrent : TestBase() {
    @Test
    fun testBrokenSharedFlowAssertion() = runTest {
        repeat(1000) {
            coroutineScope {
                val signalBus = MutableSharedFlow<CompletableJob>()
                val collector = launch(Dispatchers.Default, start = CoroutineStart.UNDISPATCHED) {
                    signalBus.collect { it.complete() }
                }
                val job = launch(start = CoroutineStart.UNDISPATCHED) {
                    try {
                        awaitCancellation()
                    } catch (_: CancellationException) {
                        signalBus.emit(Job())
                    }
                }
                job.cancelAndJoin()
                val collectionSuccessful = Job()
                signalBus.emit(collectionSuccessful)
                withTimeout(1.seconds) {
                    collectionSuccessful.join()
                }
                collector.cancel()
            }
        }
    }
}
