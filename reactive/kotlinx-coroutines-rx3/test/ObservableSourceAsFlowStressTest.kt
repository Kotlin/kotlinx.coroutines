/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx3

import io.reactivex.rxjava3.core.*
import io.reactivex.rxjava3.exceptions.*
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
