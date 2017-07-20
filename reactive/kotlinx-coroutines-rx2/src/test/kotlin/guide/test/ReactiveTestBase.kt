/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package guide.test

import io.reactivex.Scheduler
import io.reactivex.disposables.Disposable
import io.reactivex.plugins.RxJavaPlugins
import org.junit.After
import org.junit.Before
import java.util.concurrent.TimeUnit

open class ReactiveTestBase {
    @Before
    fun setup() {
        RxJavaPlugins.setIoSchedulerHandler(Handler)
        RxJavaPlugins.setComputationSchedulerHandler(Handler)
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
        worker.schedule(trackTask(run), delay, unit)
}
