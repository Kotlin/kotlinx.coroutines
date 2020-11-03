package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import org.junit.Test
import java.util.*
import java.util.concurrent.CyclicBarrier
import java.util.concurrent.atomic.AtomicInteger
import kotlin.concurrent.thread
import kotlin.random.Random
import kotlin.test.*

class SegmentQueueTest : TestBase() {
    @Test
    fun testSimpleTest() {
        val q = SegmentBasedQueue<Int>()
        assertEquals(1, q.numberOfSegments)
        assertNull(q.dequeue())
        q.enqueue(1)
        assertEquals(1, q.numberOfSegments)
        q.enqueue(2)
        assertEquals(2, q.numberOfSegments)
        assertEquals(1, q.dequeue())
        assertEquals(2, q.numberOfSegments)
        assertEquals(2, q.dequeue())
        assertEquals(1, q.numberOfSegments)
        assertNull(q.dequeue())
    }

    @Test
    fun testSegmentRemoving() {
        val q = SegmentBasedQueue<Int>()
        q.enqueue(1)
        val s = q.enqueue(2)
        q.enqueue(3)
        assertEquals(3, q.numberOfSegments)
        s!!.removeSegment()
        assertEquals(2, q.numberOfSegments)
        assertEquals(1, q.dequeue())
        assertEquals(3, q.dequeue())
        assertNull(q.dequeue())
    }

    @Test
    fun testRemoveHeadSegment() {
        val q = SegmentBasedQueue<Int>()
        q.enqueue(1)
        val s = q.enqueue(2)
        assertEquals(1, q.dequeue())
        q.enqueue(3)
        s!!.removeSegment()
        assertEquals(3, q.dequeue())
        assertNull(q.dequeue())
    }

    @Test
    fun testClose() {
        val q = SegmentBasedQueue<Int>()
        q.enqueue(1)
        assertEquals(0, q.close().id)
        assertEquals(null, q.enqueue(2))
        assertEquals(1, q.dequeue())
        assertEquals(null, q.dequeue())
    }

    @Test
    fun stressTest() {
        val q = SegmentBasedQueue<Int>()
        val expectedQueue = ArrayDeque<Int>()
        val r = Random(0)
        repeat(1_000_000 * stressTestMultiplier) {
            if (r.nextBoolean()) { // add
                val el = r.nextInt()
                q.enqueue(el)
                expectedQueue.add(el)
            } else { // remove
                assertEquals(expectedQueue.poll(), q.dequeue())
                q.checkHeadPrevIsCleaned()
            }
        }
    }

    @Test
    fun testRemoveSegmentsSerial() = stressTestRemoveSegments(false)

    @Test
    fun testRemoveSegmentsRandom() = stressTestRemoveSegments(true)

    private fun stressTestRemoveSegments(random: Boolean) {
        val N = 100_000 * stressTestMultiplier
        val T = 10
        val q = SegmentBasedQueue<Int>()
        val segments = (1..N).map { q.enqueue(it)!! }.toMutableList()
        if (random) segments.shuffle()
        assertEquals(N, q.numberOfSegments)
        val nextSegmentIndex = AtomicInteger()
        val barrier = CyclicBarrier(T)
        (1..T).map {
            thread {
                barrier.await()
                while (true) {
                    val i = nextSegmentIndex.getAndIncrement()
                    if (i >= N) break
                    segments[i].removeSegment()
                }
            }
        }.forEach { it.join() }
        assertEquals(2, q.numberOfSegments)
    }
}