/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
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
class ChannelUndeliveredElementSelectOldStressTest(private val kind: TestChannelKind) : TestBase() {
    companion object {
        @Parameterized.Parameters(name = "{0}")
        @JvmStatic
        fun params(): Collection<Array<Any>> =
            TestChannelKind.values()
                .filter { !it.viaBroadcast }
                .map { arrayOf<Any>(it) }
    }

    private val iterationDurationMs = 100L
    private val testIterations = 20 * stressTestMultiplier // 2 sec

    private val dispatcher = newFixedThreadPoolContext(2, "ChannelAtomicCancelStressTest")
    private val scope = CoroutineScope(dispatcher)

    private val channel = kind.create<Data> { it.failedToDeliver() }
    private val senderDone = Channel<Boolean>(1)
    private val receiverDone = Channel<Boolean>(1)

    @Volatile
    private var lastReceived = -1L

    private var stoppedSender = 0L
    private var stoppedReceiver = 0L

    private var sentCnt = 0L // total number of send attempts
    private var receivedCnt = 0L // actually received successfully
    private var dupCnt = 0L // duplicates (should never happen)
    private val failedToDeliverCnt = atomic(0L) // out of sent

    private val modulo = 1 shl 25
    private val mask = (modulo - 1).toLong()
    private val sentStatus = ItemStatus() // 1 - send norm, 2 - send select, +2 - did not throw exception
    private val receivedStatus = ItemStatus() // 1-6 received
    private val failedStatus = ItemStatus() // 1 - failed

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
            if (!done.trySend(true).isSuccess)
                error(IllegalStateException("failed to offer to done channel"))
        }
    }

    @Test
    fun testAtomicCancelStress() = runBlocking {
        println("=== ChannelAtomicCancelStressTest $kind")
        var nextIterationTime = System.currentTimeMillis() + iterationDurationMs
        var iteration = 0
        launchSender()
        launchReceiver()
        while (!hasError()) {
            if (System.currentTimeMillis() >= nextIterationTime) {
                nextIterationTime += iterationDurationMs
                iteration++
                verify(iteration)
                if (iteration % 10 == 0) printProgressSummary(iteration)
                if (iteration >= testIterations) break
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

    private suspend fun verify(iteration: Int) {
        stopSender()
        drainReceiver()
        stopReceiver()
        try {
            assertEquals(0, dupCnt)
            assertEquals(sentCnt - failedToDeliverCnt.value, receivedCnt)
        } catch (e: Throwable) {
            printProgressSummary(iteration)
            printErrorDetails()
            throw e
        }
        sentStatus.clear()
        receivedStatus.clear()
        failedStatus.clear()
    }

    private fun printProgressSummary(iteration: Int) {
        println("--- ChannelAtomicCancelStressTest $kind -- $iteration of $testIterations")
        println("              Sent $sentCnt times to channel")
        println("          Received $receivedCnt times from channel")
        println(" Failed to deliver ${failedToDeliverCnt.value} times")
        println("    Stopped sender $stoppedSender times")
        println("  Stopped receiver $stoppedReceiver times")
        println("        Duplicated $dupCnt deliveries")
    }

    private fun printErrorDetails() {
        val min = minOf(sentStatus.min, receivedStatus.min, failedStatus.min)
        val max = maxOf(sentStatus.max, receivedStatus.max, failedStatus.max)
        for (x in min..max) {
            val sentCnt = if (sentStatus[x] != 0) 1 else 0
            val receivedCnt = if (receivedStatus[x] != 0) 1 else 0
            val failedToDeliverCnt = failedStatus[x]
            if (sentCnt - failedToDeliverCnt != receivedCnt) {
                println("!!! Error for value $x: " +
                    "sentStatus=${sentStatus[x]}, " +
                    "receivedStatus=${receivedStatus[x]}, " +
                    "failedStatus=${failedStatus[x]}"
                )
            }
        }
    }


    private fun launchSender() {
        sender = scope.launch(start = CoroutineStart.ATOMIC) {
            cancellable(senderDone) {
                var counter = 0
                while (true) {
                    val trySendData = Data(sentCnt++)
                    sentStatus[trySendData.x] = 1
                    selectOld<Unit> { channel.onSend(trySendData) {} }
                    sentStatus[trySendData.x] = 3
                    when {
                        // must artificially slow down LINKED_LIST sender to avoid overwhelming receiver and going OOM
                        kind == TestChannelKind.UNLIMITED -> while (sentCnt > lastReceived + 100) yield()
                        // yield periodically to check cancellation on conflated channels
                        kind.isConflated -> if (counter++ % 100 == 0) yield()
                    }
                }
            }
        }
    }

    private suspend fun stopSender() {
        stoppedSender++
        sender.cancelAndJoin()
        senderDone.receive()
    }

    private fun launchReceiver() {
        receiver = scope.launch(start = CoroutineStart.ATOMIC) {
            cancellable(receiverDone) {
                while (true) {
                   selectOld<Unit> {
                        channel.onReceive { receivedData ->
                            receivedData.onReceived()
                            receivedCnt++
                            val received = receivedData.x
                            if (received <= lastReceived)
                                dupCnt++
                            lastReceived = received
                            receivedStatus[received] = 1
                        }
                    }
                }
            }
        }
    }

    private suspend fun drainReceiver() {
        while (!channel.isEmpty) yield() // burn time until receiver gets it all
    }

    private suspend fun stopReceiver() {
        stoppedReceiver++
        receiver.cancelAndJoin()
        receiverDone.receive()
    }

    private inner class Data(val x: Long) {
        private val firstFailedToDeliverOrReceivedCallTrace = atomic<Exception?>(null)

        fun failedToDeliver() {
            val trace = if (TRACING_ENABLED) Exception("First onUndeliveredElement() call") else DUMMY_TRACE_EXCEPTION
            if (firstFailedToDeliverOrReceivedCallTrace.compareAndSet(null, trace)) {
                failedToDeliverCnt.incrementAndGet()
                failedStatus[x] = 1
                return
            }
            throw IllegalStateException("onUndeliveredElement()/onReceived() notified twice", firstFailedToDeliverOrReceivedCallTrace.value!!)
        }

        fun onReceived() {
            val trace = if (TRACING_ENABLED) Exception("First onReceived() call") else DUMMY_TRACE_EXCEPTION
            if (firstFailedToDeliverOrReceivedCallTrace.compareAndSet(null, trace)) return
            throw IllegalStateException("onUndeliveredElement()/onReceived() notified twice", firstFailedToDeliverOrReceivedCallTrace.value!!)
        }
    }

    inner class ItemStatus {
        private val a = ByteArray(modulo)
        private val _min = atomic(Long.MAX_VALUE)
        private val _max = atomic(-1L)

        val min: Long get() = _min.value
        val max: Long get() = _max.value

        operator fun set(x: Long, value: Int) {
            a[(x and mask).toInt()] = value.toByte()
            _min.update { y -> minOf(x, y) }
            _max.update { y -> maxOf(x, y) }
        }

        operator fun get(x: Long): Int = a[(x and mask).toInt()].toInt()

        fun clear() {
            if (_max.value < 0) return
            for (x in _min.value.._max.value) a[(x and mask).toInt()] = 0
            _min.value = Long.MAX_VALUE
            _max.value = -1L
        }
    }
}

private const val TRACING_ENABLED = false // Change to `true` to enable the tracing
private val DUMMY_TRACE_EXCEPTION = Exception("The tracing is disabled; please enable it by changing the `TRACING_ENABLED` constant to `true`.")
