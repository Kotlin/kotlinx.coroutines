package kotlinx.coroutines

import kotlinx.coroutines.flow.MutableSharedFlow
import kotlinx.coroutines.testing.*
import kotlin.test.*

class SharedFlowCommonStressTest : TestBase() {
    @Test
    fun testBrokenSharedFlowAssertion() = runTest {
        repeat(1000) {
            coroutineScope {
                val signalBus = MutableSharedFlow<Int>()
                val collector = launch(Dispatchers.Default, start = CoroutineStart.UNDISPATCHED) {
                    signalBus.collect{}
                }
                val job = launch(start = CoroutineStart.UNDISPATCHED) {
                    try {
                        awaitCancellation()
                    } catch (_: CancellationException) {
                        signalBus.emit(0)
                    }
                }
                job.cancelAndJoin()
                signalBus.emit(1)
                collector.cancel()
            }
        }
    }
}
