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
 * Tests resource transfer via channel send & receive operations, including their select versions,
 * using `onUndeliveredElement` to detect lost resources and close them properly.
 */
@RunWith(Parameterized::class)
class ChannelUndeliveredElementStressTest(private val kind: TestChannelKind) : TestBase() {
    companion object {
        @Parameterized.Parameters(name = "{0}")
        @JvmStatic
        fun params(): Collection<Array<Any>> =
            TestChannelKind.values()
                .filter { !it.viaBroadcast }
                .map { arrayOf<Any>(it) }
    }

    private val testSeconds = 3 * stressTestMultiplier

    private val dispatcher = newFixedThreadPoolContext(2, "ChannelAtomicCancelStressTest")
    private val scope = CoroutineScope(dispatcher)

    private val channel = kind.create<Data> { it.failedToDeliver() }
    private val senderDone = Channel<Boolean>(1)
    private val receiverDone = Channel<Boolean>(1)

    private var lastReceived = -1L

    private var stoppedSender = 0L
    private var stoppedReceiver = 0L

    private var sentCnt = 0L // total number of send attempts
    private var receivedCnt = 0L // actually received successfully
    private var dupCnt = 0L // duplicates (should never happen)
    private val failedToDeliverCnt = atomic(0L) // out of sent

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
        println("=== ChannelAtomicCancelStressTest $kind")
        var nextVerify = System.currentTimeMillis() + 1000L
        var seconds = 0
        launchSender()
        launchReceiver()
        while (!hasError()) {
            if (System.currentTimeMillis() >= nextVerify) {
                nextVerify += 1000L
                seconds++
                println("--- ChannelAtomicCancelStressTest $kind --- $seconds seconds")
                printProgressAndVerify()
                if (seconds >= testSeconds) break
                launchSender()
                launchReceiver()
            }
            when (Random.nextInt(3)) {
                0 -> { // cancel & restart sender
                    stopSender()
                    launchSender()
                }
                1 -> { // cancel & restart receiver
                    stopReceiver()
                    launchReceiver()
                }
                2 -> yield() // just yield (burn a little time)
            }
        }
    }

    private suspend fun printProgressAndVerify() {
        stopSender()
        stopReceiver()
        println("              Sent $sentCnt times to channel")
        println("          Received $receivedCnt times from channel")
        println(" Failed to deliver ${failedToDeliverCnt.value} times")
        println("    Stopped sender $stoppedSender times")
        println("  Stopped receiver $stoppedReceiver times")
        println("        Duplicated $dupCnt deliveries")
        assertEquals(0, dupCnt)
        assertEquals(sentCnt - failedToDeliverCnt.value, receivedCnt)
    }

    private fun launchSender() {
        sender = scope.launch(start = CoroutineStart.ATOMIC) {
            cancellable(senderDone) {
                var counter = 0
                while (true) {
                    val trySendData = Data(sentCnt++)
                    when (Random.nextInt(2)) {
                        0 -> channel.send(trySendData)
                        1 -> select<Unit> { channel.onSend(trySendData) {} }
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
                    val receivedData = when (Random.nextInt(6)) {
                        0 -> channel.receive()
                        1 -> select { channel.onReceive { it } }
                        2 -> channel.receiveOrNull() ?: error("Should not be closed")
                        3 -> select { channel.onReceiveOrNull { it ?: error("Should not be closed") } }
                        4 -> channel.receiveOrClosed().value
                        5 -> {
                            val iterator = channel.iterator()
                            check(iterator.hasNext()) { "Should not be closed" }
                            iterator.next()
                        }
                        else -> error("cannot happen")
                    }
                    receivedCnt++
                    val received = receivedData.x
                    if (received <= lastReceived)
                        dupCnt++
                    lastReceived = received
                }
            }
        }
    }

    private inner class Data(val x: Long) {
        private val failedToDeliver = atomic(false)

        fun failedToDeliver() {
            check(failedToDeliver.compareAndSet(false, true)) { "onUndeliveredElement notified twice" }
            failedToDeliverCnt.incrementAndGet()
        }
    }

    private suspend fun stopReceiver() {
        stoppedReceiver++
        receiver.cancel()
        receiverDone.receive()
    }
}
