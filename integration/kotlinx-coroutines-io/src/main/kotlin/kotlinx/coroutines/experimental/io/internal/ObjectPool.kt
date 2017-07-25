package kotlinx.coroutines.experimental.io.internal

import kotlinx.coroutines.experimental.io.ByteBufferChannel.Companion.ReservedSize
import java.nio.*
import java.util.concurrent.atomic.*

internal const val BufferSize = 4096
internal val DirectBufferObjectPool: ObjectPool<ReadWriteBufferState.Initial> = ObjectPoolImpl(1024, {
    ReadWriteBufferState.Initial(ByteBuffer.allocateDirect(BufferSize), ReservedSize)
})

internal val DirectBufferNoPool: ObjectPool<ReadWriteBufferState.Initial> = NoPool({
    ReadWriteBufferState.Initial(ByteBuffer.allocateDirect(BufferSize), ReservedSize)
})

internal class ObjectPoolImpl<T : Any>(override val capacity: Int, private val producer: () -> T, private val disposer: (T) -> Unit = {}) : ObjectPool<T> {
    init {
        require(capacity > 0) { "capacity should be positive but it is $capacity" }
        require(capacity <= MaxCapacity) { "capacity should be less or equal to $MaxCapacity but it is $capacity"}
    }

    @Volatile
    private var top: Long = 0L

    // zero index is reserved for both
    private val instances = AtomicReferenceArray<T?>(capacity * Multiplier)
    private val next = IntArray(capacity * Multiplier)
    private val arraySize = capacity * Multiplier

    override fun borrow(): T {
        return tryPop() ?: producer()
    }

    override fun recycle(instance: T) {
        if (!push(instance)) {
            disposer(instance)
        }
    }

    override fun dispose() {
        while (true) {
            val instance = tryPop() ?: return
            disposer(instance)
        }
    }

    private fun push(instance: T): Boolean {
        val base = (Math.abs(System.identityHashCode(instance) * Magic) % arraySize).coerceAtLeast(1)

        for (i in 0..Multiplier2Minus1) {
            val index = ((base + i) % arraySize).coerceAtLeast(1)
            if (instances.compareAndSet(index, null, instance)) {
                pushTop(index)
                return true
            }
        }

        return false
    }

    private fun tryPop(): T? {
        val index = popTop()
        if (index == 0) {
            return null
        }

        return instances.getAndSet(index, null)
    }

    private fun pushTop(index: Int) {
        require(index > 0)

        while (true) {
            val oldTop = top
            val topVersion = (oldTop shr 32 and 0xffffffffL) + 1L
            val topIndex = (oldTop and 0xffffffffL).toInt()

            val newTop = topVersion shl 32 or index.toLong()
            next[index] = topIndex

            if (Top.compareAndSet(this, oldTop, newTop)) {
                return
            }
        }
    }

    private fun popTop(): Int {
        while (true) {
            val t = top

            if (t == 0L) return 0

            val newVersion = (t shr 32 and 0xffffffffL) + 1L
            val topIndex = (t and 0xffffffffL).toInt()

            if (topIndex == 0) return 0

            val next = next[topIndex]

            val newTop = newVersion shl 32 or next.toLong()

            if (Top.compareAndSet(this, t, newTop)) {
                return topIndex
            }
        }
    }

    companion object {
        private const val Multiplier = 4
        private const val Multiplier2Minus1 = Multiplier * 2 - 1
        private const val Magic = 3

        const val MaxCapacity = Int.MAX_VALUE / Multiplier

        private val Top = longUpdater(ObjectPoolImpl<*>::top)
    }
}

internal interface ObjectPool<T : Any> {
    val capacity: Int

    fun borrow(): T
    fun recycle(instance: T)
    fun dispose()
}

internal class NoPool<T : Any>(val producer : () -> T) : ObjectPool<T> {
    override val capacity: Int get() = 0

    override fun borrow(): T {
        return producer()
    }

    override fun recycle(instance: T) {
    }

    override fun dispose() {
    }
}