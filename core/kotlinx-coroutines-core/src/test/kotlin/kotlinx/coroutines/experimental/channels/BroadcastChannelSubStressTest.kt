/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.timeunit.*
import org.junit.*
import org.junit.runner.*
import org.junit.runners.*
import java.util.concurrent.atomic.*
import kotlin.coroutines.experimental.*

/**
 * Creates a broadcast channel and repeatedly opens new subscription, receives event, closes it,
 * to stress test the logic of opening the subscription
 * to broadcast channel while events are being concurrently sent to it.
 */
@RunWith(Parameterized::class)
class BroadcastChannelSubStressTest(
    val kind: TestBroadcastChannelKind
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
        val ctx = coroutineContext + DefaultDispatcher
        val sender =
            launch(context = ctx + CoroutineName("Sender")) {
                while (isActive) {
                    broadcast.send(sentTotal.incrementAndGet())
                }
            }
        val receiver =
            launch(context = ctx + CoroutineName("Receiver")) {
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
        withTimeout(5, TimeUnit.SECONDS) {
            sender.cancelAndJoin()
            receiver.cancelAndJoin()
        }
    }
}