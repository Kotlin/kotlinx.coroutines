package kotlinx.coroutines.experimental.io.internal

import java.nio.*

sealed class ReadWriteBufferState {
    abstract val backingBuffer: ByteBuffer
    abstract val capacity: RingBufferCapacity

    open val idle: Boolean get() = false

    open val readBuffer: ByteBuffer get() = throw IllegalStateException("read buffer is not available in state $this")
    open val writeBuffer: ByteBuffer get() = throw IllegalStateException("write buffer is not available in state $this")

    internal open fun startReading(): ReadWriteBufferState = throw IllegalStateException("Reading is not available in state $this")
    internal open fun startWriting(): ReadWriteBufferState = throw IllegalStateException("Writing is not available in state $this")

    internal open fun stopReading(): ReadWriteBufferState = throw IllegalStateException("Unable to stop reading in state $this")
    internal open fun stopWriting(): ReadWriteBufferState = throw IllegalStateException("Unable to stop writing in state $this")

    object IdleEmpty : ReadWriteBufferState() {
        override val backingBuffer: ByteBuffer get() = Empty
        override val idle: Boolean get() = true

        override fun toString() = "IDLE(empty)"
        override val capacity: RingBufferCapacity get() = RingBufferCapacity.Empty
    }

    class Initial(override val backingBuffer: ByteBuffer, reservedSize: Int) : ReadWriteBufferState() {
        override val writeBuffer: ByteBuffer = backingBuffer.slice()
        override val readBuffer: ByteBuffer = writeBuffer.duplicate()
        override val capacity = RingBufferCapacity(backingBuffer.capacity() - reservedSize)

        private val readingState = Reading(backingBuffer, readBuffer, { concurrent }, { idleState }, capacity)
        private val writingState = Writing(backingBuffer, writeBuffer, { concurrent }, { idleState }, capacity)

        private val concurrent: ConcurrentReadingAndWriting = ConcurrentReadingAndWriting(backingBuffer, readBuffer, writeBuffer, { writingState }, { readingState }, capacity)
        private val idleState: IdleNonEmpty = IdleNonEmpty(backingBuffer, readingState, writingState, this, capacity)

        override fun startReading() = readingState
        override fun startWriting() = writingState

        override val idle: Boolean get() = error("Not available for initial state")

        override fun toString() = "Initial"
    }

    class IdleNonEmpty internal constructor(override val backingBuffer: ByteBuffer, private val reading: ReadWriteBufferState, private val writing: ReadWriteBufferState, internal val initial: Initial, override val capacity: RingBufferCapacity) : ReadWriteBufferState() {
        override fun startReading() = reading
        override fun startWriting() = writing
        override val idle: Boolean get() = true

        override fun toString() = "IDLE(with buffer)"
    }

    class Reading internal constructor(override val backingBuffer: ByteBuffer, override val readBuffer: ByteBuffer, private val withWriting: () -> ConcurrentReadingAndWriting, private val withoutReading: () -> IdleNonEmpty, override val capacity: RingBufferCapacity) : ReadWriteBufferState() {
        override fun startWriting() = withWriting()
        override fun stopReading() = withoutReading()

        override fun startReading() = throw IllegalStateException("Read operation is already in progress")

        override fun toString() = "Reading"
    }

    class Writing internal constructor(override val backingBuffer: ByteBuffer, override val writeBuffer: ByteBuffer, private val withReading: () -> ConcurrentReadingAndWriting, val withoutWriting: () -> IdleNonEmpty, override val capacity: RingBufferCapacity) : ReadWriteBufferState() {
        override fun startReading() = withReading()
        override fun stopWriting() = withoutWriting()

        override fun startWriting() = throw IllegalStateException("Write operation is already in progress")

        override fun toString() = "Writing"
    }

    class ConcurrentReadingAndWriting internal constructor(override val backingBuffer: ByteBuffer, override val readBuffer: ByteBuffer, override val writeBuffer: ByteBuffer, private val _stopReading: () -> Writing, private val _stopWriting: () -> Reading, override val capacity: RingBufferCapacity) : ReadWriteBufferState() {
        override fun stopReading() = _stopReading()
        override fun stopWriting() = _stopWriting()

        override fun startReading() = throw IllegalStateException("Read operation is already in progress")
        override fun startWriting() = throw IllegalStateException("Write operation is already in progress")

        override fun toString() = "Reading+Writing"
    }

    object Terminated : ReadWriteBufferState() {
        override val backingBuffer: ByteBuffer
            get() = Closed

        override val capacity: RingBufferCapacity
            get() = RingBufferCapacity.Empty

        override fun toString() = "Terminated"
    }

    companion object {
        val Empty: ByteBuffer = ByteBuffer.allocate(0)
        val Closed: ByteBuffer = ByteBuffer.allocate(0)
    }
}