/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.jdk9

import kotlinx.coroutines.*
import kotlinx.coroutines.CancellationException
import org.junit.*
import java.util.concurrent.*

class AwaitTest: TestBase() {

    /** Tests that calls to [awaitFirst] (and, thus, to the rest of these functions) throw [CancellationException] and
     * unsubscribe from the publisher when their [Job] is cancelled. */
    @Test
    fun testAwaitCancellation() = runTest {
        expect(1)
        val publisher = Flow.Publisher<Int> { s ->
            s.onSubscribe(object : Flow.Subscription {
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

}