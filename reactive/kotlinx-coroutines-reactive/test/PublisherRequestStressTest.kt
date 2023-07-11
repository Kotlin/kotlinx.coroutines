/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.flow.Flow
import org.junit.*
import org.reactivestreams.*
import java.util.concurrent.*
import java.util.concurrent.atomic.*
import kotlin.coroutines.*
import kotlin.random.*

/**
 * This stress-test is self-contained reproducer for the race in [Flow.asPublisher] extension
 * that was originally reported in the issue
 * [#2109](https://github.com/Kotlin/kotlinx.coroutines/issues/2109).
 * The original reproducer used a flow that loads a file using AsynchronousFileChannel
 * (that issues completion callbacks from multiple threads)
 * and uploads it to S3 via Amazon SDK, which internally uses netty for I/O
 * (which uses a single thread for connection-related callbacks).
 *
 * This stress-test essentially mimics the logic in multiple interacting threads: several emitter threads that form
 * the flow and a single requesting thread works on the subscriber's side to periodically request more
 * values when the number of items requested drops below the threshold.
 */
@Suppress("ReactiveStreamsSubscriberImplementation")
class PublisherRequestStressTest : TestBase() {

    private val testDurationSec = 3 * stressTestMultiplier

    // Original code in Amazon SDK uses 4 and 16 as low/high watermarks.
    // These constants were chosen so that problem reproduces asap with particular this code.
    private val minDemand = 8L
    private val maxDemand = 16L

    private val nEmitThreads = 4

    private val emitThreadNo = AtomicInteger()

    private val emitPool = Executors.newFixedThreadPool(nEmitThreads) { r ->
        Thread(r, "PublisherRequestStressTest-emit-${emitThreadNo.incrementAndGet()}")
    }

    private val reqPool = Executors.newSingleThreadExecutor { r ->
        Thread(r, "PublisherRequestStressTest-req")
    }

    private val nextValue = AtomicLong(0)

    @After
    fun tearDown() {
        emitPool.shutdown()
        reqPool.shutdown()
        emitPool.awaitTermination(10, TimeUnit.SECONDS)
        reqPool.awaitTermination(10, TimeUnit.SECONDS)
    }

    private lateinit var subscription: Subscription

    @Test
    fun testRequestStress() {
        val expectedValue = AtomicLong(0)
        val requestedTill = AtomicLong(0)
        val callingOnNext = AtomicInteger()

        val publisher = mtFlow().asPublisher()
        var error = false
        
        publisher.subscribe(object : Subscriber<Long> {
            private var demand = 0L // only updated from reqPool

            override fun onComplete() {
                // Typically unreached, but, rarely, `emitPool` may shut down before the cancellation is performed.
            }

            override fun onSubscribe(sub: Subscription) {
                subscription = sub
                maybeRequestMore()
            }

            private fun maybeRequestMore() {
                if (demand >= minDemand) return
                val nextDemand = Random.nextLong(minDemand + 1..maxDemand)
                val more = nextDemand - demand
                demand = nextDemand
                requestedTill.addAndGet(more)
                subscription.request(more)
            }

            override fun onNext(value: Long) {
                check(callingOnNext.getAndIncrement() == 0) // make sure it is not concurrent
                // check for expected value
                check(value == expectedValue.get())
                // check that it does not exceed requested values
                check(value < requestedTill.get())
                val nextExpected = value + 1
                expectedValue.set(nextExpected)
                // send more requests from request thread
                reqPool.execute {
                    demand-- // processed an item
                    maybeRequestMore()
                }
                callingOnNext.decrementAndGet()
            }

            override fun onError(ex: Throwable?) {
                error = true
                error("Failed", ex)
            }
        })
        var prevExpected = -1L
        for (second in 1..testDurationSec) {
            if (error) break
            Thread.sleep(1000)
            val expected = expectedValue.get()
            println("$second: expectedValue = $expected")
            check(expected > prevExpected) // should have progress
            prevExpected = expected
        }
        if (!error) {
            subscription.cancel()
            runBlocking {
                (subscription as AbstractCoroutine<*>).join()
            }
        }
    }

    private fun mtFlow(): Flow<Long> = flow {
        while (currentCoroutineContext().isActive) {
            emit(aWait())
        }
    }

    private suspend fun aWait(): Long = suspendCancellableCoroutine { cont ->
        emitPool.execute(Runnable {
            cont.resume(nextValue.getAndIncrement())
        })
    }
}