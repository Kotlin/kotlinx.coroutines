package kotlinx.coroutines.internal

import kotlinx.atomicfu.*

/**
 * This queue implementation is based on [SegmentList] for testing purposes and is organized as follows. Essentially,
 * the [SegmentBasedQueue] is represented as an infinite array of segments, each stores one element (see [OneElementSegment]).
 * Both [enqueue] and [dequeue] operations increment the corresponding global index ([enqIdx] for [enqueue] and
 * [deqIdx] for [dequeue]) and work with the indexed by this counter cell. Since both operations increment the indices
 * at first, there could be a race: [enqueue] increments [enqIdx], then [dequeue] checks that the queue is not empty
 * (that's true) and increments [deqIdx], looking into the corresponding cell after that; however, the cell is empty
 * because the [enqIdx] operation has not been put its element yet. To make the queue non-blocking, [dequeue] can mark
 * the cell with [BROKEN] token and retry the operation, [enqueue] at the same time should restart as well; this way,
 * the queue is obstruction-free.
 */
internal class SegmentBasedQueue<T> {
    private val head: AtomicRef<OneElementSegment<T>>
    private val tail: AtomicRef<OneElementSegment<T>>

    private val enqIdx = atomic(0L)
    private val deqIdx = atomic(0L)

    init {
        val s = OneElementSegment<T>(0, null, 2)
        head = atomic(s)
        tail = atomic(s)
    }

    // Returns the segments associated with the enqueued element, or `null` if the queue is closed.
    fun enqueue(element: T): OneElementSegment<T>? {
        while (true) {
            val curTail = this.tail.value
            val enqIdx = this.enqIdx.getAndIncrement()
            val segmentOrClosed = this.tail.findSegmentAndMoveForward(id = enqIdx, startFrom = curTail, createNewSegment = ::createSegment)
            if (segmentOrClosed.isClosed) return null
            val s = segmentOrClosed.segment
            if (s.element.value === BROKEN) continue
            if (s.element.compareAndSet(null, element)) return s
        }
    }

    fun dequeue(): T? {
        while (true) {
            if (this.deqIdx.value >= this.enqIdx.value) return null
            val curHead = this.head.value
            val deqIdx = this.deqIdx.getAndIncrement()
            val segmentOrClosed = this.head.findSegmentAndMoveForward(id = deqIdx, startFrom = curHead, createNewSegment = ::createSegment)
            if (segmentOrClosed.isClosed) return null
            val s = segmentOrClosed.segment
            s.cleanPrev()
            if (s.id > deqIdx) continue
            var el = s.element.value
            if (el === null) {
                if (s.element.compareAndSet(null, BROKEN)) continue
                else el = s.element.value
            }
            if (el === BROKEN) continue
            return el as T
        }
    }

    // `enqueue` should return `null` after the queue is closed
    fun close(): OneElementSegment<T> {
        val s = this.tail.value.close()
        var cur = s
        while (true) {
            cur.element.compareAndSet(null, BROKEN)
            cur = cur.prev ?: break
        }
        return s
    }

    val numberOfSegments: Int get() {
        var cur = head.value
        var i = 1
        while (true) {
            cur = cur.nextOrClosed.run {
                if (isClosed || node === null) return i
                this.node!!
            }
            i++
        }
    }

    fun checkHeadPrevIsCleaned() {
        check(head.value.prev === null)
    }
}

private fun <T> createSegment(id: Long, prev: OneElementSegment<T>?) = OneElementSegment(id, prev, 0)

internal class OneElementSegment<T>(id: Long, prev: OneElementSegment<T>?, pointers: Int) : Segment<OneElementSegment<T>>(id, prev, pointers) {
    val element = atomic<Any?>(null)

    override val maxSlots get() = 1

    fun removeSegment() {
        element.value = BROKEN
        onSlotCleaned()
    }
}

private val BROKEN = Symbol("BROKEN")