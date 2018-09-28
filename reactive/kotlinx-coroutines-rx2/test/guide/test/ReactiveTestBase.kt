/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.rx2.guide.test

import io.reactivex.*
import io.reactivex.disposables.*
import io.reactivex.plugins.*
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.guide.test.*
import org.junit.*
import java.util.concurrent.*

open class ReactiveTestBase {
    @Before
    fun setup() {
        RxJavaPlugins.setIoSchedulerHandler(Handler)
        RxJavaPlugins.setComputationSchedulerHandler(Handler)
        ignoreLostThreads(
            "RxComputationThreadPool-",
            "RxCachedThreadScheduler-",
            "RxCachedWorkerPoolEvictor-",
            "RxSchedulerPurge-")
    }

    @After
    fun tearDown() {
        RxJavaPlugins.setIoSchedulerHandler(null)
        RxJavaPlugins.setComputationSchedulerHandler(null)
    }
}

private object Handler : io.reactivex.functions.Function<Scheduler, Scheduler> {
    override fun apply(t: Scheduler): Scheduler = WrapperScheduler(t)
}

private class WrapperScheduler(private val scheduler: Scheduler) : Scheduler() {
    override fun createWorker(): Worker = WrapperWorker(scheduler.createWorker())
}

private class WrapperWorker(private val worker: Scheduler.Worker) : Scheduler.Worker() {
    override fun isDisposed(): Boolean = worker.isDisposed
    override fun dispose() = worker.dispose()
    override fun schedule(run: Runnable, delay: Long, unit: TimeUnit): Disposable =
        worker.schedule(wrapTask(run), delay, unit)
}
