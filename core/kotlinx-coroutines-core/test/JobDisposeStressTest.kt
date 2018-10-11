/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import org.junit.Test
import kotlin.concurrent.thread

/**
 * Tests concurrent cancel & dispose of the jobs.
 */
class JobDisposeStressTest: TestBase() {
    private val TEST_DURATION = 3 * stressTestMultiplier // seconds

    @Volatile
    private var done = false
    @Volatile
    private var job: TestJob? = null
    @Volatile
    private var handle: DisposableHandle? = null

    @Volatile
    private var exception: Throwable? = null

    private fun testThread(name: String, block: () -> Unit): Thread =
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
            while (!done) {
                val job = this.job ?: continue
                val result = job.cancel()
                // Always returns true, TestJob never completes
                check(result)
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
    }

    @Suppress("DEPRECATION_ERROR")
    private class TestJob : JobSupport(active = true)
}