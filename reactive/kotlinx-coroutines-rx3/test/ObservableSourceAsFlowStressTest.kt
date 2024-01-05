package kotlinx.coroutines.rx3

import kotlinx.coroutines.testing.*
import io.reactivex.rxjava3.core.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import org.junit.*
import java.util.concurrent.*

class ObservableSourceAsFlowStressTest : TestBase() {

    private val iterations = 100 * stressTestMultiplierSqrt

    @Before
    fun setup() {
        ignoreLostThreads("RxComputationThreadPool-", "RxCachedWorkerPoolEvictor-", "RxSchedulerPurge-")
    }

    @Test
    fun testAsFlowCancellation() = runTest {
        repeat(iterations) {
            val latch = Channel<Unit>(1)
            var i = 0
            val observable = Observable.interval(100L, TimeUnit.MICROSECONDS)
                .doOnNext {  if (++i > 100) latch.trySend(Unit) }
            val job = observable.asFlow().launchIn(CoroutineScope(Dispatchers.Default))
            latch.receive()
            job.cancelAndJoin()
        }
    }
}
