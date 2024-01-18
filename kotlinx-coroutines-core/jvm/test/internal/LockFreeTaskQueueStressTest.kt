package kotlinx.coroutines.internal

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import org.junit.runner.*
import org.junit.runners.*
import java.util.concurrent.*
import kotlin.concurrent.*
import kotlin.test.*

// Tests many short queues to stress copy/resize
@RunWith(Parameterized::class)
class LockFreeTaskQueueStressTest(
    private val nConsumers: Int
) : TestBase() {
    companion object {
        @Parameterized.Parameters(name = "nConsumers={0}")
        @JvmStatic
        fun params(): Collection<Int> = listOf(1, 3)
    }

    private val singleConsumer = nConsumers == 1

    private val nSeconds = 3 * stressTestMultiplier
    private val nProducers = 4
    private val batchSize = 100

    private val batch = atomic(0)
    private val produced = atomic(0L)
    private val consumed = atomic(0L)
    private var expected = LongArray(nProducers)

    private val queue = atomic<LockFreeTaskQueue<Item>?>(null)
    private val done = atomic(0)
    private val doneProducers = atomic(0)

    private val barrier = CyclicBarrier(nProducers + nConsumers + 1)

    private class Item(val producer: Int, val index: Long)

    @Test
    fun testStress() {
        val threads = mutableListOf<Thread>()
        threads += thread(name = "Pacer", start = false) {
            while (done.value == 0) {
                queue.value = LockFreeTaskQueue(singleConsumer)
                batch.value = 0
                doneProducers.value = 0
                barrier.await() // start consumers & producers
                barrier.await() // await consumers & producers
            }
            queue.value = null
            println("Pacer done")
            barrier.await() // wakeup the rest
        }
        threads += List(nConsumers) { consumer ->
            thread(name = "Consumer-$consumer", start = false) {
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
                        if (singleConsumer) {
                            // This check only properly works in single-consumer case
                            val eItem = expected[item.producer]++
                            if (eItem != item.index) error("Expected $eItem but got ${item.index} from Producer-${item.producer}")
                        }
                    }
                    barrier.await()
                }
                println("Consumer-$consumer done")
            }
        }
        threads += List(nProducers) { producer ->
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