/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import org.junit.*
import org.junit.runner.*
import org.junit.runners.*
import java.util.concurrent.atomic.*

/**
 * Creates a broadcast channel and repeatedly opens new subscription, receives event, closes it,
 * to stress test the logic of opening the subscription
 * to broadcast channel while events are being concurrently sent to it.
 */
@RunWith(Parameterized::class)
class BroadcastChannelSubStressTest(
    private val kind: TestBroadcastChannelKind
) : TestBase() {
    companion object {
        @Parameterized.Parameters(name = "{0}")
        @JvmStatic
        fun params(): Collection<Array<Any>> =
            TestBroadcastChannelKind.values().map { arrayOf<Any>(it) }
    }

    private val nSeconds = 5 * stressTestMultiplier
    private val broadcast = kind.create<Long>()

    private val sentTotal = AtomicLong()
    private val receivedTotal = AtomicLong()

    @Test
    fun testStress() = runBlocking {
        println("--- BroadcastChannelSubStressTest $kind")
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
            val curSent = sentTotal.get()
            println("${sec + 1}: Sent $curSent, received ${receivedTotal.get()}")
            check(curSent > prevSent) { "Send stalled at $curSent events" }
            prevSent = curSent
        }
        withTimeout(5000) {
            sender.cancelAndJoin()
            receiver.cancelAndJoin()
        }
    }
}