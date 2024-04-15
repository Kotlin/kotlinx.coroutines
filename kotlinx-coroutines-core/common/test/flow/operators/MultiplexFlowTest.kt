package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.testing.*
import kotlin.test.*

class MultiplexFlowTest : TestBase() {
    @Test
    fun firstKeys_collects() = runTest {
        expect(1)
        lateinit var multiplex: MultiplexFlow<Int, String>
        val multiplexJob = launch(start = CoroutineStart.UNDISPATCHED) {
            multiplex = MultiplexFlow(this@launch) { keys ->
                expect(3)
                assertEquals(setOf(1, 2), keys)
                flowOf()
            }
        }
        val collectJob = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            multiplex[1, 2].collect {}
        }
        collectJob.join()
        multiplexJob.cancel()
        finish(4)
    }

    @Test
    fun newKeys_recollects() = runTest {
        expect(1)
        lateinit var multiplex: MultiplexFlow<Int, String>
        val multiplexJob = launch(start = CoroutineStart.UNDISPATCHED) {
            multiplex = MultiplexFlow(this@launch) { keys ->
                when (keys) {
                    setOf(1, 2) -> expect(3)
                    setOf(1, 2, 3) -> expect(5)
                    else -> expectUnreached()
                }
                flowOf()
            }
        }
        val collectJob1 = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            multiplex[1, 2].collect {}
        }
        yield()
        val collectJob2 = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(4)
            multiplex[2, 3].collect {}
        }
        collectJob1.join()
        collectJob2.join()
        multiplexJob.cancel()
        finish(6)
    }

    @Test
    fun existingKey_doesNotCollect() = runTest {
        expect(1)
        lateinit var multiplex: MultiplexFlow<Int, String>
        val multiplexJob = launch(start = CoroutineStart.UNDISPATCHED) {
            multiplex = MultiplexFlow(this@launch) { keys ->
                expect(3)
                assertEquals(setOf(1, 2), keys)
                flowOf()
            }
        }
        val collectJob1 = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            multiplex[1, 2].collect {}
        }
        yield()
        val collectJob2 = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(4)
            multiplex[1, 2].collect {}
        }
        collectJob1.join()
        collectJob2.join()
        multiplexJob.cancel()
        finish(5)
    }

    @Test
    fun notCollected_doesNotCollect() = runTest {
        expect(1)
        val multiplexJob = launch(start = CoroutineStart.UNDISPATCHED) {
            MultiplexFlow<Int, String>(this@launch) {
                expectUnreached()
                flowOf()
            }
        }
        yield()
        multiplexJob.cancel()
        finish(2)
    }

    @Test
    fun newData_emitsRelevantFlows() = runTest {
        expect(1)
        lateinit var multiplex: MultiplexFlow<Int, String>
        val multiplexJob = launch(start = CoroutineStart.UNDISPATCHED) {
            multiplex = MultiplexFlow(this@launch, replay = 2 /* value + finish */) { keys ->
                when (keys) {
                    setOf(1) -> expect(3)
                    setOf(1, 2) -> expect(5)
                    setOf(1, 2, 3) -> {
                        expect(7)
                        return@MultiplexFlow flowOf(mapOf(1 to "1", 2 to "2"))
                    }

                    else -> expectUnreached()
                }
                MutableSharedFlow() // Avoid finishing the flow.
            }
        }
        val collectJob1 = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            multiplex[1].collect {
                expect(8)
                assertEquals("1", it)
            }
        }
        yield()
        val collectJob2 = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(4)
            multiplex[2].collect {
                expect(9)
                assertEquals("2", it)
            }
        }
        yield()
        val collectJob3 = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(6)
            multiplex[3].collect {
                expectUnreached()
            }
        }
        collectJob1.join()
        collectJob2.join()
        collectJob3.join()
        multiplexJob.cancel()
        finish(10)
    }

    @Test
    fun recollect() = runTest {
        expect(1)
        lateinit var multiplex: MultiplexFlow<Int, String>
        var collections = 0
        val multiplexJob = launch(start = CoroutineStart.UNDISPATCHED) {
            multiplex = MultiplexFlow(this@launch, replay = 2 /* value + finish */) {
                when (collections) {
                    0 -> expect(3)
                    1 -> expect(6)
                    else -> expectUnreached()
                }
                collections++
                flowOf(mapOf(1 to "1")) // Avoid finish
            }
        }
        val collectJob1 = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            multiplex[1, 2].collect { expect(4) }
        }
        collectJob1.join()
        val collectJob2 = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(5)
            multiplex[1, 2].collect { expect(7) }
        }
        collectJob2.join()
        multiplexJob.cancel()
        finish(8)
    }

    @Test
    fun cancelLast_cancelsCollection() = runTest {
        expect(1)
        lateinit var multiplex: MultiplexFlow<Int, String>
        val done = Channel<Unit>()
        val multiplexJob = launch(start = CoroutineStart.UNDISPATCHED) {
            multiplex = MultiplexFlow(this@launch, replay = 2 /* value + finish */) {
                expect(3)
                MutableSharedFlow<Map<Int, String>>().onCompletion { e ->
                    expect(7)
                    assertTrue(e is CancellationException)
                    done.send(Unit)
                }
            }
        }
        val collectJob1 = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            multiplex[1, 2].collect {}
        }
        yield()
        val collectJob2 = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(4)
            multiplex[1, 2].collect {}
        }
        yield()
        expect(5)
        collectJob1.cancel()
        yield()
        expect(6) // First cancel doesn't stop collection.
        collectJob2.cancel()
        done.receive()
        expect(8)
        multiplexJob.cancel()
        finish(9)
    }

    @Test
    fun cancelLastForKey_recollectsWithoutKey() = runTest {
        expect(1)
        lateinit var multiplex: MultiplexFlow<Int, String>
        var collections = 0
        val ready = Channel<Unit>()
        val done = Channel<Unit>()
        val multiplexJob = launch(start = CoroutineStart.UNDISPATCHED) {
            multiplex = MultiplexFlow(this@launch, replay = 2 /* value + finish */) { keys ->
                when (collections) {
                    0 -> {
                        assertEquals(setOf(1), keys)
                        expect(3)
                    }

                    1 -> {
                        assertEquals(setOf(1, 2), keys)
                        expect(5)
                        ready.send(Unit)
                    }

                    2 -> {
                        assertEquals(setOf(2), keys)
                        expect(7)
                        done.send(Unit)
                    }
                }
                collections++
                MutableSharedFlow() // Avoid finish.
            }
        }
        val collectJob1 = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            multiplex[1].collect {}
        }
        yield()
        launch(start = CoroutineStart.UNDISPATCHED) {
            expect(4)
            multiplex[2].collect {}
        }
        ready.receive()
        expect(6)
        collectJob1.cancel()
        done.receive()
        expect(8)
        multiplexJob.cancel()
        finish(9)
    }

    @Test
    fun recollect_clearsCache() = runTest {}

    @Test
    fun cancelNotLast_doesNotUnregister() = runTest {}

    @Test
    fun getAllFails_flowThrows() = runTest {}

    @Test
    fun getAllFailsAnotherKey_flowThrowsAndRollbacks() = runTest {}

    @Test
    fun getAllFailsAnotherKeyTwice_allFlowsThrow() = runTest {}

    @Test
    fun collectionThrows_allFlowsThrow() = runTest {}

    @Test
    fun retryFailure_collectsAndEmitsOnNewData() = runTest {}

    @Test
    fun quickRecollection_continuesEmitting() = runTest {}

    @Test
    fun scopeCancelled_allFlowsFinish() = runTest {}

    @Test
    fun sameFlowCollectedTwice_cancelsCollectionAfterBothFinish() = runTest {}

    @Test
    fun replayZero_recollects() = runTest {}
}
