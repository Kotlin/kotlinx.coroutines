@file:OptIn(ExperimentalAtomicApi::class)

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.testing.*
import kotlin.concurrent.atomics.*
import kotlin.test.*

class ConflatedChannelCloseStressTest : TestBase() {

    private val nSenders = 2
    private val testSeconds = 3 * stressTestMultiplier

    private val curChannel = AtomicReference<Channel<Int>>(Channel(Channel.CONFLATED))
    private val sent = AtomicInt(0)
    private val closed = AtomicInt(0)
    val received = AtomicInt(0)

    val pool = newFixedThreadPoolContext(nSenders + 2, "TestStressClose")

    @AfterTest
    fun tearDown() {
        pool.close()
    }

    @Test
    fun testStressClose() = runBlocking {
        println("--- ConflatedChannelCloseStressTest with nSenders=$nSenders")
        val senderJobs = List(nSenders) { Job() }
        val senders = List(nSenders) { senderId ->
            launch(pool) {
                var x = senderId
                try {
                    while (isActive) {
                        curChannel.load().trySend(x).onSuccess {
                            x += nSenders
                            sent.incrementAndFetch()
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
                    closed.incrementAndFetch()
                    yield()
                }
            } finally {
                closerJob.cancel()
            }
        }
        val receiver = async(pool + NonCancellable) {
            while (isActive) {
                curChannel.load().receiveCatching().getOrElse {
                    it?.let { throw it }
                }
                received.incrementAndFetch()
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
        senderJobs.joinAll()
        println("waiting for closer...")
        closerJob.join()
        // close cur channel
        println("Closing channel and signalling receiver...")
        flipChannel()
        curChannel.load().close(StopException())
        /// wait for receiver do complete
        println("Waiting for receiver...")
        try {
            receiver.await()
            error("Receiver should not complete normally")
        } catch (_: StopException) {
            // ok
        }
        // print stats
        println("--- done")
        printStats()
    }

    private fun flipChannel() {
        val oldChannel = curChannel.load()
        val newChannel = Channel<Int>(Channel.CONFLATED)
        curChannel.store(newChannel)
        check(oldChannel.close())
    }

    private fun printStats() {
        println("sent ${sent.load()}, closed ${closed.load()}, received ${received.load()}")
    }

    class StopException : Exception()
}
