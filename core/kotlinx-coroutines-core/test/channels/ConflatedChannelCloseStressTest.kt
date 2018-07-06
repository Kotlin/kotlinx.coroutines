/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import org.junit.After
import org.junit.Test
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.atomic.AtomicReference
import kotlin.coroutines.experimental.*

class ConflatedChannelCloseStressTest : TestBase() {

    val nSenders = 2
    val testSeconds = 3 * stressTestMultiplier

    val curChannel = AtomicReference<ConflatedChannel<Int>>(ConflatedChannel())
    val sent = AtomicInteger()
    val closed = AtomicInteger()
    val received = AtomicInteger()

    val pool = newFixedThreadPoolContext(nSenders + 2, "TestStressClose")

    @After
    fun tearDown() {
        pool.close()
    }

    @Test
    fun testStressClose() = runBlocking<Unit> {
        println("--- ConflatedChannelCloseStressTest with nSenders=$nSenders")
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
            error("Receiver should not complete normally")
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
        check(oldChannel.close())
    }

    private fun printStats() {
        println("sent ${sent.get()}, closed ${closed.get()}, received ${received.get()}")
    }

    class StopException : Exception()
}