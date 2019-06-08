package kotlinx.coroutines.internal

import kotlinx.atomicfu.AtomicRef
import kotlinx.atomicfu.atomic
import kotlinx.atomicfu.loop

/**
 * Essentially, this segment queue is an infinite array of segments, which is represented as
 * a Michael-Scott queue of them. All segments are instances of [Segment] class and
 * follow in natural order (see [Segment.id]) in the queue.
 */
internal abstract class SegmentQueue<S: Segment<S>>() {
    private val _head: AtomicRef<S>
    /**
     * Returns the first segment in the queue.
     */
    protected val head: S get() = _head.value

    private val _tail: AtomicRef<S>
    /**
     * Returns the last segment in the queue.
     */
    protected val tail: S get() = _tail.value

    init {
        val initialSegment = newSegment(0)
        _head = atomic(initialSegment)
        _tail = atomic(initialSegment)
    }

    /**
     * The implementation should create an instance of segment [S] with the specified id
     * and initial reference to the previous one.
     */
    abstract fun newSegment(id: Long, prev: S? = null): S

    /**
     * Finds a segment with the specified [id] following by next references from the
     * [startFrom] segment. The typical use-case is reading [tail] or [head], doing some
     * synchronization, and invoking [getSegment] or [getSegmentAndMoveHead] correspondingly
     * to find the required segment.
     */
    protected fun getSegment(startFrom: S, id: Long): S? {
        // Go through `next` references and add new segments if needed,
        // similarly to the `push` in the Michael-Scott queue algorithm.
        // The only difference is that `CAS failure` means that the
        // required segment has already been added, so the algorithm just
        // uses it. This way, only one segment with each id can be in the queue.
        var cur: S = startFrom
        while (cur.id < id) {
            var curNext = cur.next
            if (curNext == null) {
                // Add a new segment.
                val newTail = newSegment(cur.id + 1, cur)
                curNext = if (cur.casNext(null, newTail)) {
                    if (cur.removed) {
                        cur.remove()
                    }
                    moveTailForward(newTail)
                    newTail
                } else {
                    cur.next!!
                }
            }
            cur = curNext
        }
        if (cur.id != id) return null
        return cur
    }

    /**
     * Invokes [getSegment] and replaces [head] with the result if its [id] is greater.
     */
    protected fun getSegmentAndMoveHead(startFrom: S, id: Long): S? {
        @Suppress("LeakingThis")
        if (startFrom.id == id) return startFrom
        val s = getSegment(startFrom, id) ?: return null
        moveHeadForward(s)
        return s
    }

    /**
     * Updates [head] to the specified segment
     * if its `id` is greater.
     */
    private fun moveHeadForward(new: S) {
        _head.loop { curHead ->
            if (curHead.id > new.id) return
            if (_head.compareAndSet(curHead, new)) {
                new.prev.value = null
                return
            }
        }
    }

    /**
     * Updates [tail] to the specified segment
     * if its `id` is greater.
     */
    private fun moveTailForward(new: S) {
        _tail.loop { curTail ->
            if (curTail.id > new.id) return
            if (_tail.compareAndSet(curTail, new)) return
        }
    }
}

/**
 * Each segment in [SegmentQueue] has a unique id and is created by [SegmentQueue.newSegment].
 * Essentially, this is a node in the Michael-Scott queue algorithm, but with
 * maintaining [prev] pointer for efficient [remove] implementation.
 */
internal abstract class Segment<S: Segment<S>>(val id: Long, prev: S?) {
    // Pointer to the next segment, updates similarly to the Michael-Scott queue algorithm.
    private val _next = atomic<S?>(null)
    val next: S? get() = _next.value
    fun casNext(expected: S?, value: S?): Boolean = _next.compareAndSet(expected, value)
    // Pointer to the previous segment, updates in [remove] function.
    val prev = atomic<S?>(null)

    /**
     * Returns `true` if this segment is logically removed from the queue.
     * The [remove] function should be called right after it becomes logically removed.
     */
    abstract val removed: Boolean

    init {
        this.prev.value = prev
    }

    /**
     * Removes this segment physically from the segment queue. The segment should be
     * logically removed (so [removed] returns `true`) at the point of invocation.
     */
    fun remove() {
        check(removed) { " The segment should be logically removed at first "}
        // Read `next` and `prev` pointers.
        var next = this._next.value ?: return // tail cannot be removed
        var prev = prev.value ?: return // head cannot be removed
        // Link `next` and `prev`.
        prev.moveNextToRight(next)
        while (prev.removed) {
            prev = prev.prev.value ?: break
            prev.moveNextToRight(next)
        }
        next.movePrevToLeft(prev)
        while (next.removed) {
            next = next.next ?: break
            next.movePrevToLeft(prev)
        }
    }

    /**
     * Updates [next] pointer to the specified segment if
     * the [id] of the specified segment is greater.
     */
    private fun moveNextToRight(next: S) {
        while (true) {
            val curNext = this._next.value as S
            if (next.id <= curNext.id) return
            if (this._next.compareAndSet(curNext, next)) return
        }
    }

    /**
     * Updates [prev] pointer to the specified segment if
     * the [id] of the specified segment is lower.
     */
    private fun movePrevToLeft(prev: S) {
        while (true) {
            val curPrev = this.prev.value ?: return
            if (curPrev.id <= prev.id) return
            if (this.prev.compareAndSet(curPrev, prev)) return
        }
    }
}