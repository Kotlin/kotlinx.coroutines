/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import java.util.concurrent.*
import kotlin.concurrent.*
import kotlin.test.*

// Tests many short queues to stress copy/resize
class LockFreeMPSCQueueStressTest : TestBase() {
    private val nSeconds = 3 * stressTestMultiplier
    private val nProducers = 4
    private val batchSize = 100

    private val batch = atomic(0)
    private val produced = atomic(0L)
    private val consumed = atomic(0L)
    private var expected = LongArray(nProducers)

    private val queue = atomic<LockFreeMPSCQueue<Item>?>(null)
    private val done = atomic(0)
    private val doneProducers = atomic(0)

    private val barrier = CyclicBarrier(nProducers + 2)

    private class Item(val producer: Int, val index: Long)

    @Test
    fun testStress() {
        val threads = mutableListOf<Thread>()
        threads += thread(name = "Pacer", start = false) {
            while (done.value == 0) {
                queue.value = LockFreeMPSCQueue()
                batch.value = 0
                doneProducers.value = 0
                barrier.await() // start consumers & producers
                barrier.await() // await consumers & producers
            }
            queue.value = null
            println("Pacer done")
            barrier.await() // wakeup the rest
        }
        threads += thread(name = "Consumer", start = false) {
            while (true) {
                barrier.await()
                val queue = queue.value ?: break
                while (true) {
                    val item = queue.removeFirstOrNull()
                    if (item == null) {
                        if (doneProducers.value == nProducers && queue.isEmpty) break // that's it
                        continue // spin to retry
                    }
                    consumed.incrementAndGet()
                    val eItem = expected[item.producer]++
                    if (eItem != item.index) error("Expected $eItem but got ${item.index} from Producer-${item.producer}")
                }
                barrier.await()
            }
            println("Consumer done")
        }
        val producers = List(nProducers) { producer ->
            thread(name = "Producer-$producer", start = false) {
                var index = 0L
                while (true) {
                    barrier.await()
                    val queue = queue.value ?: break
                    while (true) {
                        if (batch.incrementAndGet() >= batchSize) break
                        check(queue.addLast(Item(producer, index++))) // never closed
                        produced.incrementAndGet()
                    }
                    doneProducers.incrementAndGet()
                    barrier.await()
                }
                println("Producer-$producer done")
            }
        }
        threads += producers
        threads.forEach {
            it.setUncaughtExceptionHandler { t, e ->
                System.err.println("Thread $t failed: $e")
                e.printStackTrace()
                done.value = 1
                error("Thread $t failed", e)
            }
        }
        threads.forEach { it.start() }
        for (second in 1..nSeconds) {
            Thread.sleep(1000)
            println("$second: produced=${produced.value}, consumed=${consumed.value}")
            if (done.value == 1) break
        }
        done.value = 1
        threads.forEach { it.join() }
        println("T: produced=${produced.value}, consumed=${consumed.value}")
        assertEquals(produced.value, consumed.value)
    }
}