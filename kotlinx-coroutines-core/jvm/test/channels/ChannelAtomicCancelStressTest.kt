/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.selects.*
import org.junit.*
import org.junit.Assert.*
import org.junit.runner.*
import org.junit.runners.*
import java.util.*
import java.util.concurrent.atomic.*

/**
 * Tests cancel atomicity for channel send & receive operations, including their select versions.
 */
@RunWith(Parameterized::class)
class ChannelAtomicCancelStressTest(private val kind: TestChannelKind) : TestBase() {
    companion object {
        @Parameterized.Parameters(name = "{0}")
        @JvmStatic
        fun params(): Collection<Array<Any>> = TestChannelKind.values().map { arrayOf<Any>(it) }
    }

    private val TEST_DURATION = 1000L * stressTestMultiplier

    private val dispatcher = newFixedThreadPoolContext(2, "ChannelAtomicCancelStressTest")
    private val scope = CoroutineScope(dispatcher)

    private val channel = kind.create()
    private val senderDone = Channel<Boolean>(1)
    private val receiverDone = Channel<Boolean>(1)

    private var lastSent = 0
    private var lastReceived = 0

    private var stoppedSender = 0
    private var stoppedReceiver = 0

    private var missedCnt = 0
    private var dupCnt = 0

    val failed = AtomicReference<Throwable>()

    lateinit var sender: Job
    lateinit var receiver: Job

    @After
    fun tearDown() {
        dispatcher.close()
    }

    fun fail(e: Throwable) = failed.compareAndSet(null, e)

    private inline fun cancellable(done: Channel<Boolean>, block: () -> Unit) {
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
    fun testAtomicCancelStress() = runBlocking {
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

    private fun launchSender() {
        sender = scope.launch(start = CoroutineStart.ATOMIC) {
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

    private suspend fun stopSender() {
        stoppedSender++
        sender.cancel()
        senderDone.receive()
    }

    private fun launchReceiver() {
        receiver = scope.launch(start = CoroutineStart.ATOMIC) {
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

    private suspend fun stopReceiver() {
        stoppedReceiver++
        receiver.cancel()
        receiverDone.receive()
    }
}
