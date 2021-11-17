/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug.internal

import kotlinx.atomicfu.*
import kotlinx.coroutines.internal.*
import java.lang.ref.*

// This is very limited implementation, not suitable as a generic map replacement.
// It has lock-free get and put with synchronized rehash for simplicity (and better CPU usage on contention)
@OptIn(ExperimentalStdlibApi::class)
@Suppress("UNCHECKED_CAST")
internal class ConcurrentWeakMap<K : Any, V: Any>(
    /**
     * Weak reference queue is needed when a small key is mapped to a large value and we need to promptly release a
     * reference to the value when the key was already disposed.
     */
    weakRefQueue: Boolean = false
) : AbstractMutableMap<K, V>() {
    private val _size = atomic(0)
    private val core = atomic(Core(MIN_CAPACITY))
    private val weakRefQueue: ReferenceQueue<K>? = if (weakRefQueue) ReferenceQueue() else null

    override val size: Int
        get() = _size.value

    private fun decrementSize() { _size.decrementAndGet() }

    override fun get(key: K): V? = core.value.getImpl(key)

    override fun put(key: K, value: V): V? {
        var oldValue = core.value.putImpl(key, value)
        if (oldValue === REHASH) oldValue = putSynchronized(key, value)
        if (oldValue == null) _size.incrementAndGet()
        return oldValue as V?
    }

    override fun remove(key: K): V? {
        var oldValue = core.value.putImpl(key, null)
        if (oldValue === REHASH) oldValue = putSynchronized(key, null)
        if (oldValue != null) _size.decrementAndGet()
        return oldValue as V?
    }

    @Synchronized
    private fun putSynchronized(key: K, value: V?): V? {
        // Note: concurrent put leaves chance that we fail to put even after rehash, we retry until successful
        var curCore = core.value
        while (true) {
            val oldValue = curCore.putImpl(key, value)
            if (oldValue !== REHASH) return oldValue as V?
            curCore = curCore.rehash()
            core.value = curCore
        }
    }

    override val keys: MutableSet<K>
        get() = KeyValueSet { k, _ -> k }

    override val entries: MutableSet<MutableMap.MutableEntry<K, V>>
        get() = KeyValueSet { k, v -> Entry(k, v) }

    // We don't care much about clear's efficiency
    override fun clear() {
        for (k in keys) remove(k)
    }

    fun runWeakRefQueueCleaningLoopUntilInterrupted() {
        check(weakRefQueue != null) { "Must be created with weakRefQueue = true" }
        try {
            while (true) {
                cleanWeakRef(weakRefQueue.remove() as HashedWeakRef<*>)
            }
        } catch (e: InterruptedException) {
            Thread.currentThread().interrupt()
        }
    }

    private fun cleanWeakRef(w: HashedWeakRef<*>) {
        core.value.cleanWeakRef(w)
    }

    @Suppress("UNCHECKED_CAST")
    private inner class Core(private val allocated: Int) {
        private val shift = allocated.countLeadingZeroBits() + 1
        private val threshold = 2 * allocated / 3 // max fill factor at 66% to ensure speedy lookups
        private val load = atomic(0) // counts how many slots are occupied in this core
        private val keys = atomicArrayOfNulls<HashedWeakRef<K>?>(allocated)
        private val values = atomicArrayOfNulls<Any?>(allocated)

        private fun index(hash: Int) = (hash * MAGIC) ushr shift

        // get is always lock-free, unwraps the value that was marked by concurrent rehash
        fun getImpl(key: K): V? {
            var index = index(key.hashCode())
            while (true) {
                val w = keys[index].value ?: return null // not found
                val k = w.get()
                if (key == k) {
                    val value = values[index].value
                    return (if (value is Marked) value.ref else value) as V?
                }
                if (k == null) removeCleanedAt(index) // weak ref was here, but collected
                if (index == 0) index = allocated
                index--
            }
        }

        private fun removeCleanedAt(index: Int) {
            while (true) {
                val oldValue = values[index].value ?: return // return when already removed
                if (oldValue is Marked) return // cannot remove marked (rehash is working on it, will not copy)
                if (values[index].compareAndSet(oldValue, null)) { // removed
                    decrementSize()
                    return
                }
            }
        }

        // returns REHASH when rehash is needed (the value was not put)
        fun putImpl(key: K, value: V?, weakKey0: HashedWeakRef<K>? = null): Any? {
            var index = index(key.hashCode())
            var loadIncremented = false
            var weakKey: HashedWeakRef<K>? = weakKey0
            while (true) {
                val w = keys[index].value
                if (w == null) { // slot empty => not found => try reserving slot
                    if (value == null) return null // removing missing value, nothing to do here
                    if (!loadIncremented) {
                        // We must increment load before we even try to occupy a slot to avoid overfill during concurrent put
                        load.update { n ->
                            if (n >= threshold) return REHASH // the load is already too big -- rehash
                            n + 1 // otherwise increment
                        }
                        loadIncremented = true
                    }
                    if (weakKey == null) weakKey = HashedWeakRef(key, weakRefQueue)
                    if (keys[index].compareAndSet(null, weakKey)) break // slot reserved !!!
                    continue // retry at this slot on CAS failure (somebody already reserved this slot)
                }
                val k = w.get()
                if (key == k) { // found already reserved slot at index
                    if (loadIncremented) load.decrementAndGet() // undo increment, because found a slot
                    break
                }
                if (k == null) removeCleanedAt(index) // weak ref was here, but collected
                if (index == 0) index = allocated
                index--
            }
            // update value
            var oldValue: Any?
            while (true) {
                oldValue = values[index].value
                if (oldValue is Marked) return REHASH // rehash started, cannot work here
                if (values[index].compareAndSet(oldValue, value)) break
            }
            return oldValue as V?
        }

        // only one thread can rehash, but may have concurrent puts/gets
        fun rehash(): Core {
            // use size to approximate new required capacity to have at least 25-50% fill factor,
            // may fail due to concurrent modification, will retry
            retry@while (true) {
                val newCapacity = size.coerceAtLeast(MIN_CAPACITY / 4).takeHighestOneBit() * 4
                val newCore = Core(newCapacity)
                for (index in 0 until allocated) {
                    // load the key
                    val w = keys[index].value
                    val k = w?.get()
                    if (w != null && k == null) removeCleanedAt(index) // weak ref was here, but collected
                    // mark value so that it cannot be changed while we rehash to new core
                    var value: Any?
                    while (true) {
                        value = values[index].value
                        if (value is Marked) { // already marked -- good
                            value = value.ref
                            break
                        }
                        // try mark
                        if (values[index].compareAndSet(value, value.mark())) break
                    }
                    if (k != null && value != null) {
                        val oldValue = newCore.putImpl(k, value as V, w)
                        if (oldValue === REHASH) continue@retry // retry if we underestimated capacity
                        assert(oldValue == null)
                    }
                }
                return newCore // rehashed everything successfully
            }
        }

        fun cleanWeakRef(weakRef: HashedWeakRef<*>) {
            var index = index(weakRef.hash)
            while (true) {
                val w = keys[index].value ?: return // return when slots are over
                if (w === weakRef) { // found
                    removeCleanedAt(index)
                    return
                }
                if (index == 0) index = allocated
                index--
            }
        }

        fun <E> keyValueIterator(factory: (K, V) -> E): MutableIterator<E> = KeyValueIterator(factory)

        private inner class KeyValueIterator<E>(private val factory: (K, V) -> E) : MutableIterator<E> {
            private var index = -1
            private lateinit var key: K
            private lateinit var value: V

            init { findNext() }

            private fun findNext() {
                while (++index < allocated) {
                    key = keys[index].value?.get() ?: continue
                    var value = values[index].value
                    if (value is Marked) value = value.ref
                    if (value != null) {
                        this.value = value as V
                        return
                    }
                }
            }

            override fun hasNext(): Boolean = index < allocated

            override fun next(): E {
                if (index >= allocated) throw NoSuchElementException()
                return factory(key, value).also { findNext() }
            }

            override fun remove() = noImpl()
        }
    }

    private class Entry<K, V>(override val key: K, override val value: V) : MutableMap.MutableEntry<K, V> {
        override fun setValue(newValue: V): V = noImpl()
    }

    private inner class KeyValueSet<E>(
        private val factory: (K, V) -> E
    ) : AbstractMutableSet<E>() {
        override val size: Int get() = this@ConcurrentWeakMap.size
        override fun add(element: E): Boolean = noImpl()
        override fun iterator(): MutableIterator<E> = core.value.keyValueIterator(factory)
    }
}

private const val MAGIC = 2654435769L.toInt() // golden ratio
private const val MIN_CAPACITY = 16
private val REHASH = Symbol("REHASH")
private val MARKED_NULL = Marked(null)
private val MARKED_TRUE = Marked(true) // When using map as set "true" used as value, optimize its mark allocation

/**
 * Weak reference that stores the original hash code so that we can use reference queue to promptly clean them up
 * from the hashtable even in the absence of ongoing modifications.
 */
internal class HashedWeakRef<T>(
    ref: T, queue: ReferenceQueue<T>?
) : WeakReference<T>(ref, queue) {
    @JvmField
    val hash = ref.hashCode()
}

/**
 * Marked values cannot be modified. The marking is performed when rehash has started to ensure that concurrent
 * modifications (that are lock-free) cannot perform any changes and are forced to synchronize with ongoing rehash.
 */
private class Marked(@JvmField val ref: Any?)

private fun Any?.mark(): Marked = when(this) {
    null -> MARKED_NULL
    true -> MARKED_TRUE
    else -> Marked(this)
}

private fun noImpl(): Nothing {
    throw UnsupportedOperationException("not implemented")
}
