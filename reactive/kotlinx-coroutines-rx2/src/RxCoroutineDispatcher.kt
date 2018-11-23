/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.Scheduler
import io.reactivex.disposables.Disposable
import io.reactivex.schedulers.Schedulers
import kotlinx.coroutines.*
import java.util.concurrent.TimeUnit
import kotlin.coroutines.CoroutineContext

/**
 * Converts an instance of [CoroutineDispatcher] to an implementation of [Scheduler].
 * If dispatcher is instance of [SchedulerCoroutineDispatcher] it just extracts underlying [Scheduler].
 */
public fun CoroutineDispatcher.asScheduler(): Scheduler = when (this) {
    is SchedulerCoroutineDispatcher -> scheduler
    else -> CoroutineDispatcherScheduler(this)
}

/**
 * Implements [Scheduler] on top of an arbitrary [CoroutineDispatcher].
 * @param dispatcher a dispatcher.
 */
public class CoroutineDispatcherScheduler(
        /**
         * Underlying dispatcher of current [Scheduler].
         */
        public val dispatcher: CoroutineDispatcher
) : Scheduler() {

    override fun createWorker(): Worker {
        return DispatcherWorker(dispatcher)
    }

    internal class DispatcherWorker(val dispatcher: CoroutineDispatcher) : Worker(), CoroutineScope {

        private val job = Job()

        override val coroutineContext: CoroutineContext by lazy { dispatcher + job }

        override fun isDisposed(): Boolean = job.isCompleted

        override fun schedule(run: Runnable, delay: Long, unit: TimeUnit): Disposable {
            val taskJob = launch {
                delay(unit.toMillis(delay))
                run.run()
            }
            return DisposableJob(taskJob)
        }

        override fun dispose() {
            job.cancel()
            Schedulers.single()
        }
    }

    internal class DisposableJob(val job: Job) : Disposable {
        override fun isDisposed(): Boolean = job.isCompleted
        override fun dispose() = job.cancel()
    }
}
