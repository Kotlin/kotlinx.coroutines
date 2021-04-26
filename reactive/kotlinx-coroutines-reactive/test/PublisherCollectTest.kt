/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive

import kotlinx.coroutines.*
import org.junit.Test
import org.reactivestreams.*
import kotlin.test.*

class PublisherCollectTest: TestBase() {

    /** Tests the simple scenario where the publisher outputs a bounded stream of values to collect. */
    @Test
    fun testCollect() = runTest {
        val x = 100
        val xSum = x * (x + 1) / 2
        val publisher = Publisher<Int> { subscriber ->
            var requested = 0L
            var lastOutput = 0
            subscriber.onSubscribe(object: Subscription {

                override fun request(n: Long) {
                    requested += n
                    if (n <= 0) {
                        subscriber.onError(IllegalArgumentException())
                        return
                    }
                    while (lastOutput < x && lastOutput < requested) {
                        lastOutput += 1
                        subscriber.onNext(lastOutput)
                    }
                    if (lastOutput == x)
                        subscriber.onComplete()
                }

                override fun cancel() {
                    /** According to rule 3.5 of the
                     * [reactive spec](https://github.com/reactive-streams/reactive-streams-jvm/blob/v1.0.3/README.md#3.5),
                     * this method can be called by the subscriber at any point, so it's not an error if it's called
                     * in this scenario. */
                }

            })
        }
        var sum = 0
        publisher.collect {
            sum += it
        }
        assertEquals(xSum, sum)
    }

    /** Tests the behavior of [collect] when the publisher raises an error. */
    @Test
    fun testCollectThrowingPublisher() = runTest {
        val errorString = "Too many elements requested"
        val x = 100
        val xSum = x * (x + 1) / 2
        val publisher = Publisher<Int> { subscriber ->
            var requested = 0L
            var lastOutput = 0
            subscriber.onSubscribe(object: Subscription {

                override fun request(n: Long) {
                    requested += n
                    if (n <= 0) {
                        subscriber.onError(IllegalArgumentException())
                        return
                    }
                    while (lastOutput < x && lastOutput < requested) {
                        lastOutput += 1
                        subscriber.onNext(lastOutput)
                    }
                    if (lastOutput == x)
                        subscriber.onError(IllegalArgumentException(errorString))
                }

                override fun cancel() {
                    /** See the comment for the corresponding part of [testCollect]. */
                }

            })
        }
        var sum = 0
        try {
            publisher.collect {
                sum += it
            }
        } catch (e: IllegalArgumentException) {
            assertEquals(errorString, e.message)
        }
        assertEquals(xSum, sum)
    }

    /** Tests the behavior of [collect] when the action throws. */
    @Test
    fun testCollectThrowingAction() = runTest {
        val errorString = "Too many elements produced"
        val x = 100
        val xSum = x * (x + 1) / 2
        val publisher = Publisher<Int> { subscriber ->
            var requested = 0L
            var lastOutput = 0
            subscriber.onSubscribe(object: Subscription {

                override fun request(n: Long) {
                    requested += n
                    if (n <= 0) {
                        subscriber.onError(IllegalArgumentException())
                        return
                    }
                    while (lastOutput < x && lastOutput < requested) {
                        lastOutput += 1
                        subscriber.onNext(lastOutput)
                    }
                }

                override fun cancel() {
                    assertEquals(x, lastOutput)
                    expect(x + 2)
                }

            })
        }
        var sum = 0
        try {
            expect(1)
            var i = 1
            publisher.collect {
                sum += it
                i += 1
                expect(i)
                if (sum >= xSum) {
                    throw IllegalArgumentException(errorString)
                }
            }
        } catch (e: IllegalArgumentException) {
            expect(x + 3)
            assertEquals(errorString, e.message)
        }
        finish(x + 4)
    }
}