/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.jdk9

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import org.junit.Test
import java.util.concurrent.Flow as JFlow
import kotlin.test.*

class FlowAsPublisherTest : TestBase() {

    @Test
    fun testErrorOnCancellationIsReported() {
        expect(1)
        flow<Int> {
            try {
                emit(2)
            } finally {
                expect(3)
                throw TestException()
            }
        }.asPublisher().subscribe(object : JFlow.Subscriber<Int> {
            private lateinit var subscription: JFlow.Subscription

            override fun onComplete() {
                expectUnreached()
            }

            override fun onSubscribe(s: JFlow.Subscription?) {
                subscription = s!!
                subscription.request(2)
            }

            override fun onNext(t: Int) {
                expect(t)
                subscription.cancel()
            }

            override fun onError(t: Throwable?) {
                assertTrue(t is TestException)
                expect(4)
            }
        })
        finish(5)
    }

    @Test
    fun testCancellationIsNotReported() {
        expect(1)
        flow<Int>    {
            emit(2)
        }.asPublisher().subscribe(object : JFlow.Subscriber<Int> {
            private lateinit var subscription: JFlow.Subscription

            override fun onComplete() {
                expect(3)
            }

            override fun onSubscribe(s: JFlow.Subscription?) {
                subscription = s!!
                subscription.request(2)
            }

            override fun onNext(t: Int) {
                expect(t)
                subscription.cancel()
            }

            override fun onError(t: Throwable?) {
                expectUnreached()
            }
        })
        finish(4)
    }
}
