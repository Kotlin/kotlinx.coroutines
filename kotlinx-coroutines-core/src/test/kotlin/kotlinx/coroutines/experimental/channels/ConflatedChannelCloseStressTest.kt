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

import junit.framework.Assert.assertTrue
import junit.framework.Assert.fail
import kotlinx.coroutines.experimental.*
import org.junit.After
import org.junit.Test
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.atomic.AtomicReference

class ConflatedChannelCloseStressTest : TestBase() {

    val nSenders = 2
    val testSeconds = 3 * stressTestMultiplier

    val curChannel = AtomicReference<ConflatedChannel<Int>>(ConflatedChannel())
    val sent = AtomicInteger()
    val closed = AtomicInteger()
    val received = AtomicInteger()

    val pool = newFixedThreadPoolContext(nSenders + 2, "TestStressClose")

    @After
    fun tearDown() { pool[Job]!!.cancel() }

    @Test
    fun testStressClose() = runBlocking<Unit> {
        val senderJobs = List(nSenders) { Job() }
        val senders = List(nSenders) { senderId ->
            launch(pool) {
                var x = senderId
                try {
                    while (isActive) {
                        try {
                            curChannel.get().offer(x)
                            x += nSenders
                            sent.incrementAndGet()
                        } catch (e: ClosedSendChannelException) {
                            // ignore
                        }
                    }
                } finally {
                    senderJobs[senderId].cancel()
                }
            }
        }
        val closerJob = Job()
        val closer = launch(pool) {
            try {
                while (isActive) {
                    flipChannel()
                    closed.incrementAndGet()
                    yield()
                }
            } finally {
                closerJob.cancel()
            }
        }
        val receiver = async(pool) {
            while (isActive) {
                curChannel.get().receiveOrNull()
                received.incrementAndGet()
            }
        }
        // print stats while running
        repeat(testSeconds) {
            delay(1000)
            printStats()
        }
        println("Stopping")
        senders.forEach { it.cancel() }
        closer.cancel()
        // wait them to complete
        println("waiting for senders...")
        senderJobs.forEach { it.join() }
        println("waiting for closer...")
        closerJob.join()
        // close cur channel
        println("Closing channel and signalling receiver...")
        flipChannel()
        curChannel.get().close(StopException())
        /// wait for receiver do complete
        println("Waiting for receiver...")
        try {
            receiver.await()
            fail("Receiver should not complete normally")
        } catch (e: StopException) {
            // ok
        }
        // print stats
        println("--- done")
        printStats()
    }

    private fun flipChannel() {
        val oldChannel = curChannel.get()
        val newChannel = ConflatedChannel<Int>()
        curChannel.set(newChannel)
        assertTrue(oldChannel.close())
    }

    private fun printStats() {
        println("sent ${sent.get()}, closed ${closed.get()}, received ${received.get()}")
    }

    class StopException : Exception()
}