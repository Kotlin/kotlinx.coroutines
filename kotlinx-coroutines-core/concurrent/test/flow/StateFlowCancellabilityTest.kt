@file:OptIn(ExperimentalAtomicApi::class)

package kotlinx.coroutines.flow

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlin.concurrent.atomics.*
import kotlin.test.*

class StateFlowCancellabilityTest : TestBase() {
    @Test
    fun testCancellabilityNoConflation() = runTest {
        expect(1)
        val state = MutableStateFlow(0)
        val subscribed = AtomicBoolean(false)
        val lastReceived = AtomicInt(-1)
        val barrier = TwoPhaseBarrier(2)
        val job = state
            .onSubscription {
                subscribed.store(true)
                barrier.await() // 1
            }
            .onEach { i ->
                when (i) {
                    0 -> expect(2) // initial value
                    1 -> expect(3)
                    2 -> {
                        expect(4)
                        currentCoroutineContext().cancel()
                    }
                    else -> expectUnreached() // shall check for cancellation
                }
                lastReceived.store(i)
                barrier.await() // 2
                barrier.await() // 3
            }
            .launchIn(this + Dispatchers.Default)
        barrier.await() // 1
        assertTrue(subscribed.load()) // should have subscribed in the first barrier
        barrier.await() // 2
        assertEquals(0, lastReceived.load()) // should get initial value, too
        for (i in 1..3) { // emit after subscription
            state.value = i
            barrier.await() // 3, let it go
            if (i < 3) {
                barrier.await() // 2, wait for receive
                assertEquals(i, lastReceived.load()) // shall receive it
            }
        }
        job.join()
        finish(5)
    }
}
