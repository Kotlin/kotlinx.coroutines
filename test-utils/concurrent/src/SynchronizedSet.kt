package kotlinx.coroutines.testing

import kotlinx.coroutines.sync.*

class SynchronizedSet {
    private val elements = LinkedHashSet<Long>()
    private val mutex = Mutex()

    suspend fun add(value: Long) = mutex.withLock {
        elements.add(value)
    }

    suspend fun snapshot(): List<Long> = mutex.withLock { elements.toList() }

    suspend fun size() = mutex.withLock { elements.size }
}
