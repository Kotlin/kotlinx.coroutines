package kotlinx.coroutines.experimental.io.internal

class RingBufferCapacity(val totalCapacity: Int) {
    @Volatile
    var remaining = 0
        private set

    @Volatile
    var capacity = totalCapacity
        private set

    @Volatile
    var pending = 0
        private set

    // concurrent unsafe!
    fun reset() {
        remaining = 0
        pending = 0
        capacity = totalCapacity
    }

    fun resetForRead() {
        capacity = 0
        pending = 0
        remaining = totalCapacity
    }

    fun tryReadExact(n: Int): Boolean {
        while (true) {
            val remaining = remaining
            if (remaining < n) return false
            if (Remaining.compareAndSet(this, remaining, remaining - n)) return true
        }
    }

    fun tryReadAtMost(n: Int): Int {
        while (true) {
            val remaining = remaining
            val delta = minOf(n, remaining)
            if (delta == 0) return 0
            if (Remaining.compareAndSet(this, remaining, remaining - delta)) return delta
        }
    }

    fun tryWriteExact(n: Int): Boolean {
        while (true) {
            val remaining = capacity
            if (remaining < n) return false
            if (Capacity.compareAndSet(this, remaining, remaining - n)) return true
        }
    }

    fun tryWriteAtMost(n: Int): Int {
        while (true) {
            val remaining = capacity
            val delta = minOf(n, remaining)
            if (delta == 0) return 0
            if (Capacity.compareAndSet(this, remaining, remaining - delta)) return delta
        }
    }

    fun completeRead(n: Int) {
        while (true) {
            val capacity = capacity
            val newValue = capacity + n

            require(newValue <= totalCapacity) { "Completed read overflow: $capacity + $n = $newValue > $totalCapacity" }
            if (Capacity.compareAndSet(this, capacity, newValue)) break
        }
    }

    fun completeWrite(n: Int) {
        while (true) {
            val pending = pending
            val newPending = pending + n

            require(newPending <= totalCapacity) { "Complete write overflow: $pending + $n > $totalCapacity" }
            if (Pending.compareAndSet(this, pending, newPending)) break
        }
    }

    /**
     * @return true if there are bytes available for read after flush
     */
    fun flush(): Boolean {
        val pending = Pending.getAndSet(this, 0)

        while (true) {
            val remaining = remaining
            val newRemaining = remaining + pending

            if (remaining == newRemaining || Remaining.compareAndSet(this, remaining, newRemaining)) {
                return newRemaining > 0
            }
        }
    }

    fun tryLockForRelease(): Boolean {
        while (true) {
            val capacity = capacity
            if (pending > 0 || remaining > 0 || capacity != totalCapacity) return false
            if (Capacity.compareAndSet(this, capacity, 0)) return true
        }
    }

    fun isEmpty(): Boolean = capacity == totalCapacity
    fun isFull(): Boolean = capacity == 0

    companion object {
        val Empty = RingBufferCapacity(0)

        private val Remaining = intUpdater(RingBufferCapacity::remaining)
        private val Capacity = intUpdater(RingBufferCapacity::capacity)
        private val Pending = intUpdater(RingBufferCapacity::pending)
    }
}