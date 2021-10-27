/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlin.test.*

/**
 * Creates a broadcast channel and repeatedly opens new subscription, receives event, closes it,
 * to stress test the logic of opening the subscription
 * to broadcast channel while events are being concurrently sent to it.
 */
class BroadcastChannelSubStressTest: TestBase() {

    private val nSeconds = 5 * stressTestMultiplier
    private val sentTotal = atomic(0L)
    private val receivedTotal = atomic(0L)

    @Test
    fun testStress() = runMtTest {
        TestBroadcastChannelKind.values().forEach { kind ->
            println("--- BroadcastChannelSubStressTest $kind")
            val broadcast = kind.create<Long>()
            val sender =
                launch(context = Dispatchers.Default + CoroutineName("Sender")) {
                    while (isActive) {
                        broadcast.send(sentTotal.incrementAndGet())
                    }
                }
            val receiver =
                launch(context = Dispatchers.Default + CoroutineName("Receiver")) {
                    var last = -1L
                    while (isActive) {
                        val channel = broadcast.openSubscription()
                        val i = channel.receive()
                        check(i >= last) { "Last was $last, got $i" }
                        if (!kind.isConflated) check(i != last) { "Last was $last, got it again" }
                        receivedTotal.incrementAndGet()
                        last = i
                        channel.cancel()
                    }
                }
            var prevSent = -1L
            repeat(nSeconds) { sec ->
                delay(1000)
                val curSent = sentTotal.value
                println("${sec + 1}: Sent $curSent, received ${receivedTotal.value}")
                check(curSent > prevSent) { "Send stalled at $curSent events" }
                prevSent = curSent
            }
            withTimeout(5000) {
                sender.cancelAndJoin()
                receiver.cancelAndJoin()
            }
        }
    }
}
