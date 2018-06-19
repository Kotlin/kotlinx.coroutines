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

package kotlinx.coroutines.experimental

import org.junit.Test
import kotlin.concurrent.thread

/**
 * Tests concurrent cancel & dispose of the jobs.
 */
class JobDisposeTest: TestBase() {
    private val TEST_DURATION = 3 * stressTestMultiplier // seconds

    @Volatile
    private var done = false
    @Volatile
    private var job: TestJob? = null
    @Volatile
    private var handle: DisposableHandle? = null

    @Volatile
    private var exception: Throwable? = null

    fun testThread(name: String, block: () -> Unit): Thread =
        thread(start = false, name = name, block = block).apply {
            setUncaughtExceptionHandler { t, e ->
                exception = e
                println("Exception in ${t.name}: $e")
                e.printStackTrace()
            }
        }

    @Test
    fun testConcurrentDispose() {
        // create threads
        val threads = mutableListOf<Thread>()
        threads += testThread("creator") {
            while (!done) {
                val job = TestJob()
                val handle = job.invokeOnCompletion(onCancelling = true) { /* nothing */ }
                this.job = job // post job to cancelling thread
                this.handle = handle // post handle to concurrent disposer thread
                handle.dispose() // dispose of handle from this thread (concurrently with other disposer)
            }
        }
        threads += testThread("canceller") {
            var prevJob: Job? = null
            while (!done) {
                val job = this.job ?: continue
                val result = job.cancel()
                if (job != prevJob) {
                    check(result) // must have returned true
                    prevJob = job
                } else
                    check(!result) // must have returned false
            }
        }
        threads += testThread("disposer") {
            while (!done) {
                handle?.dispose()
            }
        }
        // start threads
        threads.forEach { it.start() }
        // wait
        for (i in 1..TEST_DURATION) {
            println("$i: Running")
            Thread.sleep(1000)
            if (exception != null) break
        }
        // done
        done = true
        // join threads
        threads.forEach { it.join() }
        // rethrow exception if any
        exception?.let { throw it }
    }

    private class TestJob : JobSupport(active = true)
}