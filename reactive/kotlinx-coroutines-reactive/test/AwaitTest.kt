/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive

import kotlinx.coroutines.*
import kotlinx.coroutines.sync.*
import org.junit.*
import org.reactivestreams.*

class AwaitTest: TestBase() {

    /** Tests that calls to [awaitFirst] (and, thus, to the rest of these functions) throw [CancellationException] and
     * unsubscribe from the publisher when their [Job] is cancelled. */
    @Test
    fun testAwaitCancellation() = runTest {
        expect(1)
        val publisher = Publisher<Int> { s ->
            s.onSubscribe(object: Subscription {
                override fun request(n: Long) {
                    expect(3)
                }

                override fun cancel() {
                    expect(5)
                }
            })
        }
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            try {
                expect(2)
                publisher.awaitFirst()
            } catch (e: CancellationException) {
                expect(6)
                throw e
            }
        }
        expect(4)
        job.cancelAndJoin()
        finish(7)
    }

    @Test
    fun testAwaitCancellationPerformedSerially() = runTest {
        val requestCompletion = Mutex(locked = true)
        val subscriptionStarted = Mutex(locked = true)
        expect(1)
        val publisher = Publisher<Int> { s ->
            s.onSubscribe(object : Subscription {
                override fun request(n: Long) {
                    expect(2)
                    subscriptionStarted.unlock()
                    runBlocking { requestCompletion.lock() }
                    expect(4)
                }

                override fun cancel() {
                    expect(5)
                }
            })
        }
        val job = launch(Dispatchers.IO) {
            try {
                publisher.awaitFirst()
            } catch (e: CancellationException) {
                expect(6)
                throw e
            }
        }
        subscriptionStarted.lock()
        expect(3)

        job.cancel()
        requestCompletion.unlock()
        job.join()

        finish(7)
    }
}
