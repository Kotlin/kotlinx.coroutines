package kotlinx.coroutines

import kotlinx.coroutines.flow.*
import kotlinx.coroutines.testing.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/**
 * Stress tests for rendezvous [MutableSharedFlow]s (no replay, no buffer) in which some emitters get cancelled
 * while waiting for collectors, leaving gaps in the queue of waiting emitters.
 *
 * Emitters cancelled while waiting may or may not have delivered their values, so only the values of
 * non-cancelled emitters are checked.
 * A hang is detected with a timeout.
 */
class SharedFlowStressTestConcurrent : TestBase() {
    private val nRepeats = 1000 * stressTestMultiplier

    @Test
    fun testBrokenSharedFlowAssertion() = runTest {
        repeat(nRepeats) {
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

    /** A cancelled emitter between two non-cancelled ones must not cause the later value to be lost. */
    @Test
    fun testCancelledEmitterInTheMiddle() = runTest {
        repeat(nRepeats) {
            coroutineScope {
                val flow = MutableSharedFlow<Signal>()
                val collectors = launchCollectors(flow, 1)
                val first = Signal(1)
                val last = Signal(1)
                val emitters = listOf(
                    launch(start = CoroutineStart.UNDISPATCHED) { flow.emit(first) },
                    launchEmitterAndCancel(flow, Signal(1)),
                    launch(start = CoroutineStart.UNDISPATCHED) { flow.emit(last) },
                )
                withTimeout(1.seconds) {
                    first.awaitReceivedByAll()
                    last.awaitReceivedByAll()
                    emitters.joinAll()
                }
                collectors.forEach { it.cancel() }
            }
        }
    }

    /** Several collectors racing past a cancelled emitter must all receive the value of the next emitter. */
    @Test
    fun testSeveralCollectorsPassCancelledEmitter() = runTest {
        repeat(nRepeats) {
            coroutineScope {
                val nCollectors = 2
                val flow = MutableSharedFlow<Signal>()
                val collectors = launchCollectors(flow, nCollectors)
                launchEmitterAndCancel(flow, Signal(nCollectors))
                val signal = Signal(nCollectors)
                val emitter = launch(start = CoroutineStart.UNDISPATCHED) { flow.emit(signal) }
                withTimeout(1.seconds) {
                    signal.awaitReceivedByAll()
                    emitter.join()
                }
                collectors.forEach { it.cancel() }
            }
        }
    }

    /**
     * A collector that leaves while others are passing a cancelled emitter
     * must not cause the value of the next emitter to be lost for the remaining collector.
     */
    @Test
    fun testCollectorLeavesNearCancelledEmitter() = runTest {
        repeat(nRepeats) {
            coroutineScope {
                val flow = MutableSharedFlow<Signal>()
                val (staying, leaving) = launchCollectors(flow, 2)
                launchEmitterAndCancel(flow, Signal(2))
                val signal = Signal(2)
                val emitter = launch(start = CoroutineStart.UNDISPATCHED) { flow.emit(signal) }
                leaving.cancel()
                withTimeout(1.seconds) {
                    signal.receivedBy[0].join()
                    emitter.join()
                }
                staying.cancel()
            }
        }
    }

    /**
     * When the last collector leaves, the waiting emitters must be resumed, even if a cancelled emitter is first in
     * the queue, and the flow must keep working for new collectors, which must not observe stale values.
     */
    @Test
    fun testLastCollectorLeavesNearCancelledEmitter() = runTest {
        repeat(nRepeats) {
            coroutineScope {
                val flow = MutableSharedFlow<Signal>()
                val oldCollectors = launchCollectors(flow, 1)
                launchEmitterAndCancel(flow, Signal(1))
                val emitter = launch(start = CoroutineStart.UNDISPATCHED) { flow.emit(Signal(1)) }
                oldCollectors.forEach { it.cancel() }
                withTimeout(1.seconds) {
                    emitter.join() // either received or dropped due to having no subscribers, but not stuck
                }
                val firstReceived = CompletableDeferred<Signal>()
                val newCollector = launch(Dispatchers.Default, start = CoroutineStart.UNDISPATCHED) {
                    flow.collect { firstReceived.complete(it) }
                }
                val signal = Signal(1)
                withTimeout(1.seconds) {
                    flow.emit(signal)
                    assertSame(signal, firstReceived.await())
                }
                newCollector.cancel()
            }
        }
    }

    /** A value that records which of the collectors have received it. */
    private class Signal(nCollectors: Int) {
        val receivedBy: List<CompletableJob> = List(nCollectors) { Job() }

        suspend fun awaitReceivedByAll() = receivedBy.joinAll()
    }

    /** Launches [n] collectors in [Dispatchers.Default]; when this function returns, all of them are subscribed. */
    private fun CoroutineScope.launchCollectors(flow: SharedFlow<Signal>, n: Int): List<Job> = List(n) { i ->
        launch(Dispatchers.Default, start = CoroutineStart.UNDISPATCHED) {
            flow.collect { it.receivedBy[i].complete() }
        }
    }

    /** Starts emitting [value] and cancels the emitter right away, racing with the collectors that try to receive it. */
    private fun CoroutineScope.launchEmitterAndCancel(flow: MutableSharedFlow<Signal>, value: Signal): Job =
        launch(start = CoroutineStart.UNDISPATCHED) { flow.emit(value) }.also { it.cancel() }
}
