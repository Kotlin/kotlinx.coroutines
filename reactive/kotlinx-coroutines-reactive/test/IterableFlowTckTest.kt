/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("UNCHECKED_CAST")

package kotlinx.coroutines.reactive

import kotlinx.coroutines.flow.*
import org.junit.*
import org.reactivestreams.*
import org.reactivestreams.tck.*

import org.junit.Assert.*
import org.reactivestreams.Subscription
import org.reactivestreams.Subscriber
import java.util.ArrayList
import java.util.concurrent.*
import java.util.concurrent.CountDownLatch
import java.util.concurrent.ForkJoinPool.commonPool

class IterableFlowTckTest : PublisherVerification<Long>(TestEnvironment()) {

    private fun generate(num: Long): Array<Long> {
        return Array(if (num >= Integer.MAX_VALUE) 1000000 else num.toInt()) { it.toLong() }
    }

    override fun createPublisher(elements: Long): Publisher<Long> {
        return generate(elements).asIterable().asFlow().asPublisher()
    }

    @Suppress("SubscriberImplementation")
    override fun createFailedPublisher(): Publisher<Long>? {
        /*
         * This is a hack for our adapter structure:
         * Tests assume that calling "collect" is enough for publisher to fail and it is not
         * true for our implementation
         */
        val pub = { error(42) }.asFlow().asPublisher()
        return Publisher { subscriber ->
            pub.subscribe(object : Subscriber<Long> by subscriber as Subscriber<Long> {
                override fun onSubscribe(s: Subscription) {
                    subscriber.onSubscribe(s)
                    s.request(1)
                }
            })
        }
    }

    @Test
    fun testStackOverflowTrampoline() {
        val latch = CountDownLatch(1)
        val collected = ArrayList<Long>()
        val toRequest = 1000L
        val array = generate(toRequest)
        val publisher = array.asIterable().asFlow().asPublisher()

        publisher.subscribe(object : Subscriber<Long> {
            private lateinit var s: Subscription

            override fun onSubscribe(s: Subscription) {
                this.s = s
                s.request(1)
            }

            override fun onNext(aLong: Long) {
                collected.add(aLong)

                s.request(1)
            }

            override fun onError(t: Throwable) {

            }

            override fun onComplete() {
                latch.countDown()
            }
        })

        latch.await(5, TimeUnit.SECONDS)
        assertEquals(collected, array.toList())
    }

    @Test
    fun testConcurrentRequest() {
        val latch = CountDownLatch(1)
        val collected = ArrayList<Long>()
        val n = 50000L
        val array = generate(n)
        val publisher = array.asIterable().asFlow().asPublisher()

        publisher.subscribe(object : Subscriber<Long> {
            private var s: Subscription? = null

            override fun onSubscribe(s: Subscription) {
                this.s = s
                for (i in 0 until n) {
                    commonPool().execute { s.request(1) }
                }
            }

            override fun onNext(aLong: Long) {
                collected.add(aLong)
            }

            override fun onError(t: Throwable) {

            }

            override fun onComplete() {
                latch.countDown()
            }
        })

        latch.await(50, TimeUnit.SECONDS)
        assertEquals(array.toList(), collected)
    }

    @Ignore
    override fun required_spec309_requestZeroMustSignalIllegalArgumentException() {
    }

    @Ignore
    override fun required_spec309_requestNegativeNumberMustSignalIllegalArgumentException() {
    }

    @Ignore
    override fun required_spec312_cancelMustMakeThePublisherToEventuallyStopSignaling() {
        // This test has a bug in it
    }
}
