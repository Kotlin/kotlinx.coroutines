/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.selects.*
import org.junit.After
import org.junit.Test
import org.junit.runner.*
import org.junit.runners.*
import kotlin.random.Random
import kotlin.test.*

/**
 * Tests cancel atomicity for channel send & receive operations, including their select versions.
 */
@RunWith(Parameterized::class)
class ChannelResourceCancelStressTest(private val kind: TestChannelKind) : TestBase() {
    companion object {
        @Parameterized.Parameters(name = "{0}")
        @JvmStatic
        fun params(): Collection<Array<Any>> = TestChannelKind.values().map { arrayOf<Any>(it) }
    }

    private val TEST_DURATION = 1000L * stressTestMultiplier

    private val dispatcher = newFixedThreadPoolContext(2, "ChannelAtomicCancelStressTest")
    private val scope = CoroutineScope(dispatcher)

    private val channel = kind.create<Resource<Data>>()
    private val senderDone = Channel<Boolean>(1)
    private val receiverDone = Channel<Boolean>(1)

    private var lastReceived = -1

    private var stoppedSender = 0
    private var stoppedReceiver = 0

    private var sentCnt = 0 // total number of send attempts
    private var receivedCnt = 0 // actually received successfully
    private var dupCnt = 0 // duplicates (should never happen)
    private val cancelledCnt = atomic(0) // out of sent

    lateinit var sender: Job
    lateinit var receiver: Job

    @After
    fun tearDown() {
        dispatcher.close()
    }

    private inline fun cancellable(done: Channel<Boolean>, block: () -> Unit) {
        try {
            block()
        } finally {
            if (!done.offer(true))
                error(IllegalStateException("failed to offer to done channel"))
        }
    }

    @Test
    fun testAtomicCancelStress() = runBlocking {
        println("--- ChannelAtomicCancelStressTest $kind")
        val deadline = System.currentTimeMillis() + TEST_DURATION
        launchSender()
        launchReceiver()
        while (System.currentTimeMillis() < deadline && !hasError()) {
            when (Random.nextInt(3)) {
                0, 1 -> { // cancel & restart sender
                    stopSender()
                    launchSender()
                }
//                0, 1 -> { // cancel & restart receiver
//                    stopReceiver()
//                    launchReceiver()
//                }
                2 -> yield() // just yield (burn a little time)
            }
        }
        stopSender()
        stopReceiver()
        println("            Sent $sentCnt times to channel")
        println("        Received $receivedCnt times from channel")
        println("       Cancelled ${cancelledCnt.value} deliveries")
        println("  Stopped sender $stoppedSender times")
        println("Stopped receiver $stoppedReceiver times")
        println("      Duplicated $dupCnt deliveries")
        assertEquals(0, dupCnt)
        assertEquals(sentCnt - cancelledCnt.value, receivedCnt)
    }

    private fun launchSender() {
        sender = scope.launch(start = CoroutineStart.ATOMIC) {
            cancellable(senderDone) {
                var counter = 0
                while (true) {
                    val trySendResource = Resource(Data(sentCnt++)) {
                        it.cancel()
                    }

                    when (Random.nextInt(2)) {
                        0, 1 -> channel.send(trySendResource)
//                        1 -> select { channel.onSend(trySendResource) {} }
                        else -> error("cannot happen")
                    }
                    when {
                        // must artificially slow down LINKED_LIST sender to avoid overwhelming receiver and going OOM
                        kind == TestChannelKind.LINKED_LIST -> while (sentCnt > lastReceived + 100) yield()
                        // yield periodically to check cancellation on conflated channels
                        kind.isConflated -> if (counter++ % 100 == 0) yield()
                    }
                }
            }
        }
    }

    private suspend fun stopSender() {
        stoppedSender++
        sender.cancel()
        senderDone.receive()
    }

    private fun launchReceiver() {
        receiver = scope.launch(start = CoroutineStart.ATOMIC) {
            cancellable(receiverDone) {
                while (true) {
                    val receivedResource = when (Random.nextInt(2)) {
                        0, 1 -> channel.receive()
//                        1 -> select { channel.onReceive { it } }
                        else -> error("cannot happen")
                    }
                    receivedCnt++
                    val received = receivedResource.value.x
                    if (received <= lastReceived)
                        dupCnt++
                    lastReceived = received
                }
            }
        }
    }

    private inner class Data(val x: Int) {
        private val cancelled = atomic(false)

        fun cancel() {
            check(cancelled.compareAndSet(false, true)) { "Cancelled twice" }
            cancelledCnt.incrementAndGet()
        }
    }

    private suspend fun stopReceiver() {
        stoppedReceiver++
        receiver.cancel()
        receiverDone.receive()
    }
}
