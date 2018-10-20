/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive

import kotlinx.coroutines.*
import org.junit.*
import org.reactivestreams.*

class PublisherBackpressureTest : TestBase() {
    @Test
    fun testCancelWhileBPSuspended() = runBlocking {
        expect(1)
        val observable = publish {
            expect(5)
            send("A") // will not suspend, because an item was requested
            expect(7)
            send("B") // second requested item
            expect(9)
            try {
                send("C") // will suspend (no more requested)
            } finally {
                expect(12)
            }
            expectUnreached()
        }
        expect(2)
        var sub: Subscription? = null
        observable.subscribe(object : Subscriber<String> {
            override fun onSubscribe(s: Subscription) {
                sub = s
                expect(3)
                s.request(2) // request two items
            }

            override fun onNext(t: String) {
                when (t) {
                    "A" -> expect(6)
                    "B" -> expect(8)
                    else -> error("Should not happen")
                }
            }

            override fun onComplete() {
                expectUnreached()
            }

            override fun onError(e: Throwable) {
                expectUnreached()
            }
        })
        expect(4)
        yield() // yield to observable coroutine
        expect(10)
        sub!!.cancel() // now unsubscribe -- shall cancel coroutine (& do not signal)
        expect(11)
        yield() // shall perform finally in coroutine
        finish(13)
    }
}