/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive

import kotlinx.coroutines.*
import org.junit.*
import org.reactivestreams.*
import java.util.concurrent.atomic.*

/**
 * This test checks implementation of rule 2.7 for await methods - serial execution of subscription methods
 */
class AwaitCancellationStressTest : TestBase() {
    private val jobsToRun = 1000 * stressTestMultiplier

    @Test
    fun testRequestStress() = runTest {
        val jobs = (1..jobsToRun).map {
            launch(Dispatchers.Default) {
                testPublisher().awaitFirst()
            }
        }
        jobs.forEach { it.cancel() }
        jobs.joinAll()
    }

    private fun testPublisher() = Publisher<Int> { s ->
        val counter = AtomicInteger()
        s.onSubscribe(object : Subscription {
            override fun request(n: Long) {
                check(counter.getAndIncrement() == 0)
                Thread.sleep(10)
                counter.decrementAndGet()
            }

            override fun cancel() {
                check(counter.getAndIncrement() == 0)
                counter.decrementAndGet()
            }
        })
    }
}
