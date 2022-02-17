/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import java.util.concurrent.*
import kotlin.test.*

@Suppress("BlockingMethodInNonBlockingContext")
class StateFlowCancellabilityTest : TestBase() {
    @Test
    fun testCancellabilityNoConflation() = runTest {
        expect(1)
        val state = MutableStateFlow(0)
        var subscribed = true
        var lastReceived = -1
        val barrier = CyclicBarrier(2)
        val job = state
            .onSubscription {
                subscribed = true
                barrier.await()
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
                lastReceived = i
                barrier.await()
                barrier.await()
            }
            .launchIn(this + Dispatchers.Default)
        barrier.await()
        assertTrue(subscribed) // should have subscribed in the first barrier
        barrier.await()
        assertEquals(0, lastReceived) // should get initial value, too
        for (i in 1..3) { // emit after subscription
            state.value = i
            barrier.await() // let it go
            if (i < 3) {
                barrier.await() // wait for receive
                assertEquals(i, lastReceived) // shall receive it
            }
        }
        job.join()
        finish(5)
    }
}

