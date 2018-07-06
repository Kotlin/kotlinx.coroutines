/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.selects.select
import org.junit.Assert.assertEquals
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import java.util.*
import java.util.concurrent.atomic.AtomicReference

/**
 * Tests cancel atomicity for channel send & receive operations, including their select versions.
 */
@RunWith(Parameterized::class)
class ChannelAtomicCancelStressTest(val kind: TestChannelKind) : TestBase() {
    companion object {
        @Parameterized.Parameters(name = "{0}")
        @JvmStatic
        fun params(): Collection<Array<Any>> = TestChannelKind.values().map { arrayOf<Any>(it) }
    }

    val TEST_DURATION = 3000L * stressTestMultiplier

    val channel = kind.create()
    val senderDone = ArrayChannel<Boolean>(1)
    val receiverDone = ArrayChannel<Boolean>(1)

    var lastSent = 0
    var lastReceived = 0

    var stoppedSender = 0
    var stoppedReceiver = 0

    var missedCnt = 0
    var dupCnt = 0

    val failed = AtomicReference<Throwable>()

    lateinit var sender: Job
    lateinit var receiver: Job

    fun fail(e: Throwable) = failed.compareAndSet(null, e)

    inline fun cancellable(done: ArrayChannel<Boolean>, block: () -> Unit) {
        try {
            block()
        } catch (e: Throwable) {
            if (e !is CancellationException) fail(e)
            throw e
        } finally {
            if (!done.offer(true))
                fail(IllegalStateException("failed to offer to done channel"))
        }
    }

    @Test
    fun testAtomicCancelStress() = runBlocking<Unit> {
        println("--- ChannelAtomicCancelStressTest $kind")
        val deadline = System.currentTimeMillis() + TEST_DURATION
        launchSender()
        launchReceiver()
        val rnd = Random()
        while (System.currentTimeMillis() < deadline && failed.get() == null) {
            when (rnd.nextInt(3)) {
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
        stopSender()
        stopReceiver()
        println("            Sent $lastSent ints to channel")
        println("        Received $lastReceived ints from channel")
        println("  Stopped sender $stoppedSender times")
        println("Stopped receiver $stoppedReceiver times")
        println("          Missed $missedCnt ints")
        println("      Duplicated $dupCnt ints")
        failed.get()?.let { throw it }
        assertEquals(0, dupCnt)
        if (!kind.isConflated) {
            assertEquals(0, missedCnt)
            assertEquals(lastSent, lastReceived)
        }
    }

    fun launchSender() {
        sender = launch(CommonPool, start = CoroutineStart.ATOMIC) {
            val rnd = Random()
            cancellable(senderDone) {
                var counter = 0
                while (true) {
                    val trySend = lastSent + 1
                    when (rnd.nextInt(2)) {
                        0 -> channel.send(trySend)
                        1 -> select { channel.onSend(trySend) {} }
                        else -> error("cannot happen")
                    }
                    lastSent = trySend // update on success
                    if (counter++ % 1000 == 0) yield() // yield periodically to check cancellation on LinkedListChannel
                }
            }
        }
    }

    suspend fun stopSender() {
        stoppedSender++
        sender.cancel()
        senderDone.receive()
    }

    fun launchReceiver() {
        receiver = launch(CommonPool, start = CoroutineStart.ATOMIC) {
            val rnd = Random()
            cancellable(receiverDone) {
                while (true) {
                    val received = when (rnd.nextInt(2)) {
                        0 -> channel.receive()
                        1 -> select { channel.onReceive { it } }
                        else -> error("cannot happen")
                    }
                    val expected = lastReceived + 1
                    if (received > expected)
                        missedCnt++
                    if (received < expected)
                        dupCnt++
                    lastReceived = received
                }
            }
        }
    }

    suspend fun stopReceiver() {
        stoppedReceiver++
        receiver.cancel()
        receiverDone.receive()
    }
}
