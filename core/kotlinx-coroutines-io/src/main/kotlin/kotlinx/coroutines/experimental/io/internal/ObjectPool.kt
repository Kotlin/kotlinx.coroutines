package kotlinx.coroutines.experimental.io.internal

import java.nio.ByteBuffer
import java.util.concurrent.atomic.AtomicReferenceArray

internal interface ObjectPool<T : Any> {
    val capacity: Int
    fun borrow(): T
    fun recycle(instance: T) // can only recycle what was borrowed before
    fun dispose()
}

internal val BUFFER_SIZE = getIOIntProperty("BufferSize", 4096)
private val BUFFER_POOL_SIZE = getIOIntProperty("BufferPoolSize", 2048)
private val BUFFER_OBJECT_POOL_SIZE = getIOIntProperty("BufferObjectPoolSize", 1024)

// ------------- standard shared pool objects -------------

internal val BufferPool: ObjectPool<ByteBuffer> =
    object : ObjectPoolImpl<ByteBuffer>(BUFFER_POOL_SIZE) {
        override fun produceInstance(): ByteBuffer =
            ByteBuffer.allocateDirect(BUFFER_SIZE)
        override fun clearInstance(instance: ByteBuffer): ByteBuffer =
            instance.also { it.clear() }
        override fun validateInstance(instance: ByteBuffer) {
            require(instance.capacity() == BUFFER_SIZE)
        }
    }

internal val BufferObjectPool: ObjectPool<ReadWriteBufferState.Initial> =
    object: ObjectPoolImpl<ReadWriteBufferState.Initial>(BUFFER_OBJECT_POOL_SIZE) {
        override fun produceInstance() =
            ReadWriteBufferState.Initial(BufferPool.borrow())
        override fun disposeInstance(instance: ReadWriteBufferState.Initial) {
            BufferPool.recycle(instance.backingBuffer)
        }
    }

internal val BufferObjectNoPool: ObjectPool<ReadWriteBufferState.Initial> =
    object : NoPoolImpl<ReadWriteBufferState.Initial>() {
        override fun borrow(): ReadWriteBufferState.Initial =
            ReadWriteBufferState.Initial(ByteBuffer.allocateDirect(BUFFER_SIZE))
    }

// ------------- ObjectPoolImpl -------------

private const val MULTIPLIER = 4
private const val PROBE_COUNT = 8 // number of attepts to find a slot
private const val MAGIC = 2654435769.toInt() // fractional part of golden ratio
private const val MAX_CAPACITY = Int.MAX_VALUE / MULTIPLIER

internal abstract class ObjectPoolImpl<T : Any>(final override val capacity: Int) : ObjectPool<T> {
    init {
        require(capacity > 0) { "capacity should be positive but it is $capacity" }
        require(capacity <= MAX_CAPACITY) { "capacity should be less or equal to $MAX_CAPACITY but it is $capacity"}
    }

    protected abstract fun produceInstance(): T // factory
    protected open fun clearInstance(instance: T) = instance // optional cleaning of poped items
    protected open fun validateInstance(instance: T) {} // optional validation for recycled items
    protected open fun disposeInstance(instance: T) {} // optional destruction of unpoolable items

    @Volatile
    private var top: Long = 0L

    // closest power of 2 that is equal or larger than capacity * MULTIPLIER
    private val maxIndex = Integer.highestOneBit(capacity * MULTIPLIER - 1) * 2
    private val shift = Integer.numberOfLeadingZeros(maxIndex) + 1 // for hash function

    // zero index is reserved for both
    private val instances = AtomicReferenceArray<T?>(maxIndex + 1)
    private val next = IntArray(maxIndex + 1)

    override fun borrow(): T =
        tryPop()?.let { clearInstance(it) } ?: produceInstance()

    override fun recycle(instance: T) {
        validateInstance(instance)
        if (!tryPush(instance)) disposeInstance(instance)
    }

    override fun dispose() {
        while (true) {
            val instance = tryPop() ?: return
            disposeInstance(instance)
        }
    }

    private fun tryPush(instance: T): Boolean {
        var index = ((System.identityHashCode(instance) * MAGIC) ushr shift) + 1
        repeat (PROBE_COUNT) {
            if (instances.compareAndSet(index, null, instance)) {
                pushTop(index)
                return true
            }
            if (--index == 0) index = maxIndex
        }
        return false
    }

    private fun tryPop(): T? {
        val index = popTop()
        return if (index == 0) null else instances.getAndSet(index, null)
    }

    private fun pushTop(index: Int) {
        require(index > 0)
        while (true) { // lock-free loop on top
            val top = this.top // volatile read
            val topVersion = (top shr 32 and 0xffffffffL) + 1L
            val topIndex = (top and 0xffffffffL).toInt()
            val newTop = topVersion shl 32 or index.toLong()
            next[index] = topIndex
            if (Top.compareAndSet(this, top, newTop)) return
        }
    }

    private fun popTop(): Int {
        while (true) { // lock-free loop on top
            val top = this.top // volatile read
            if (top == 0L) return 0
            val newVersion = (top shr 32 and 0xffffffffL) + 1L
            val topIndex = (top and 0xffffffffL).toInt()
            if (topIndex == 0) return 0
            val next = next[topIndex]
            val newTop = newVersion shl 32 or next.toLong()
            if (Top.compareAndSet(this, top, newTop)) return topIndex
        }
    }

    companion object {
        // todo: replace with atomicfu, remove companion object
        private val Top = longUpdater(ObjectPoolImpl<*>::top)
    }
}

// ------------- NoPoolImpl -------------

internal abstract class NoPoolImpl<T : Any> : ObjectPool<T> {
    override val capacity: Int get() = 0
    override abstract fun borrow(): T
    override fun recycle(instance: T) {}
    override fun dispose() {}
}
