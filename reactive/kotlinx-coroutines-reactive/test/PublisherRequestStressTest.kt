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

@Suppress("ReactiveStreamsSubscriberImplementation")
class PublisherRequestStressTest : TestBase() {
    private val testDurationSec = 3 * stressTestMultiplier

    private val minDemand = 8L
    private val maxDemand = 10L
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
        val completionLatch = CountDownLatch(1)
        val callingOnNext = AtomicInteger()

        val publisher = mtFlow().asPublisher()
        var error = false
        
        publisher.subscribe(object : Subscriber<Long> {
            private var demand = 0L // only updated from reqPool

            override fun onComplete() {
                completionLatch.countDown()
            }

            override fun onSubscribe(sub: Subscription) {
                subscription = sub
                maybeRequestMore()
            }

            private fun maybeRequestMore() {
                if (demand >= minDemand) return
                val more = maxDemand - demand
                demand = maxDemand
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
        for (second in 1..testDurationSec) {
            if (error) break
            Thread.sleep(1000)
            println("$second: nextValue = ${nextValue.get()}, expectedValue = ${expectedValue.get()}")
        }
        if (!error) {
            subscription.cancel()
            completionLatch.await()
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