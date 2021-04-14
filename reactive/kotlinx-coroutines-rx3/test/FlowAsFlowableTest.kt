/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx3

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import org.junit.Test
import org.reactivestreams.*
import java.util.concurrent.*
import kotlin.test.*

@Suppress("ReactiveStreamsSubscriberImplementation")
class FlowAsFlowableTest : TestBase() {
    @Test
    fun testUnconfinedDefaultContext() {
        expect(1)
        val thread = Thread.currentThread()
        fun checkThread() {
            assertSame(thread, Thread.currentThread())
        }
        flowOf(42).asFlowable().subscribe(object : Subscriber<Int> {
            private lateinit var subscription: Subscription

            override fun onSubscribe(s: Subscription) {
                expect(2)
                subscription = s
                subscription.request(2)
            }

            override fun onNext(t: Int) {
                checkThread()
                expect(3)
                assertEquals(42, t)
            }

            override fun onComplete() {
                checkThread()
                expect(4)
            }

            override fun onError(t: Throwable?) {
                expectUnreached()
            }
        })
        finish(5)
    }

    @Test
    fun testConfinedContext() {
        expect(1)
        val threadName = "FlowAsFlowableTest.testConfinedContext"
        fun checkThread() {
            val currentThread = Thread.currentThread()
            assertTrue(currentThread.name.startsWith(threadName), "Unexpected thread $currentThread")
        }
        val completed = CountDownLatch(1)
        newSingleThreadContext(threadName).use { dispatcher ->
            flowOf(42).asFlowable(dispatcher).subscribe(object : Subscriber<Int> {
                private lateinit var subscription: Subscription

                override fun onSubscribe(s: Subscription) {
                    expect(2)
                    subscription = s
                    subscription.request(2)
                }

                override fun onNext(t: Int) {
                    checkThread()
                    expect(3)
                    assertEquals(42, t)
                }

                override fun onComplete() {
                    checkThread()
                    expect(4)
                    completed.countDown()
                }

                override fun onError(t: Throwable?) {
                    expectUnreached()
                }
            })
            completed.await()
        }
        finish(5)
    }
}
