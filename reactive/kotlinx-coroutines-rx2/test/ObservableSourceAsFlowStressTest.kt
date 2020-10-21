/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.*
import io.reactivex.exceptions.*
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import org.junit.*
import java.util.concurrent.*

class ObservableSourceAsFlowStressTest : TestBase() {

    private val maxIterations = 25
    private val collectorJobCancelDelay = 1_000L
    private val nextIterationDelay = collectorJobCancelDelay * 2

    private var jobCancelledException: Throwable? = null
    private val exceptionHandler = { throwable: Throwable ->
        jobCancelledException = extractJobCancelledException(throwable)
    }

    @Before
    fun setup() {
        ignoreLostThreads("RxComputationThreadPool-", "RxCachedWorkerPoolEvictor-", "RxSchedulerPurge-")
    }

    @Test
    fun testObservableSourceAsFlow_doesntThrowJobCancelledException() = withExceptionHandler(exceptionHandler) {
        val collectorThread = newSingleThreadContext("Collector Thread")
        val cancellerThread = newSingleThreadContext("Canceller Thread")
        val scope = CoroutineScope(Job())
        var iteration = 0

        while (jobCancelledException == null && iteration < maxIterations) {
            scope.runIteration(collectorThread, cancellerThread)
            iteration += 1

            Thread.sleep(nextIterationDelay)

            collectorThread.cancel()
            cancellerThread.cancel()
        }

        collectorThread.close()
        cancellerThread.close()
        scope.cancel()

        jobCancelledException?.also {
            throw error("ObservableSource.asFlow() cancellation caused exception in iteration # $iteration", it)
        }
    }

    private fun CoroutineScope.runIteration(
        collectorThread: ExecutorCoroutineDispatcher,
        cancellerThread: ExecutorCoroutineDispatcher
    ) {
        val outerObservable = Observable.interval(1L, TimeUnit.MILLISECONDS)
        val innerObservable = Observable.interval(1L, TimeUnit.MILLISECONDS)

        val collectorJob = launch(collectorThread) {
            outerObservable
                .asFlow()
                .flatMapLatest {
                    innerObservable.asFlow()
                }
                .collect { delay(100) }
        }

        launch(cancellerThread) {
            delay(collectorJobCancelDelay)
            collectorJob.cancel()
        }
    }

    private fun extractJobCancelledException(throwable: Throwable): Throwable? {
        if (throwable is UndeliverableException) {
            if (throwable.cause !is InterruptedException) return throwable.cause
        }

        if (throwable is InterruptedException) {
            if (throwable.cause !is InterruptedException) return throwable.cause
        }

        return throwable
    }
}
