/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlin.jvm.*

private typealias Core<E> = LockFreeTaskQueueCore<E>

/**
 * Lock-free Multiply-Producer xxx-Consumer Queue for task scheduling purposes.
 *
 * **Note 1: This queue is NOT linearizable. It provides only quiescent consistency for its operations.**
 * However, this guarantee is strong enough for task-scheduling purposes.
 * In particular, the following execution is permitted for this queue, but is not permitted for a linearizable queue:
 *
 * ```
 * Thread 1: addLast(1) = true, removeFirstOrNull() = null
 * Thread 2: addLast(2) = 2 // this operation is concurrent with both operations in the first thread
 * ```
 *
 * **Note 2: When this queue is used with multiple consumers (`singleConsumer == false`) this it is NOT lock-free.**
 * In particular, consumer spins until producer finishes its operation in the case of near-empty queue.
 * It is a very short window that could manifest itself rarely and only under specific load conditions,
 * but it still deprives this algorithm of its lock-freedom.
 */
internal open class LockFreeTaskQueue<E : Any>(
    singleConsumer: Boolean // true when there is only a single consumer (slightly faster & lock-free)
) {
    private val _cur = atomic(Core<E>(Core.INITIAL_CAPACITY, singleConsumer))

    // Note: it is not atomic w.r.t. remove operation (remove can transiently fail when isEmpty is false)
    val isEmpty: Boolean get() = _cur.value.isEmpty
    val size: Int get() = _cur.value.size

    fun close() {
        _cur.loop { cur ->
            if (cur.close()) return // closed this copy
            _cur.compareAndSet(cur, cur.next()) // move to next
        }
    }

    fun addLast(element: E): Boolean {
        _cur.loop { cur ->
            when (cur.addLast(element)) {
                Core.ADD_SUCCESS -> return true
                Core.ADD_CLOSED -> return false
                Core.ADD_FROZEN -> _cur.compareAndSet(cur, cur.next()) // move to next
            }
        }
    }

    @Suppress("UNCHECKED_CAST")
    fun removeFirstOrNull(): E? = removeFirstOrNullIf { true }

    @Suppress("UNCHECKED_CAST")
    inline fun removeFirstOrNullIf(predicate: (E) -> Boolean): E? {
        _cur.loop { cur ->
            val result = cur.removeFirstOrNullIf(predicate)
            if (result !== Core.REMOVE_FROZEN) return result as E?
            _cur.compareAndSet(cur, cur.next())
        }
    }

    // Used for validation in tests only
    fun <R> map(transform: (E) -> R): List<R> = _cur.value.map(transform)

    // Used for validation in tests only
    fun isClosed(): Boolean = _cur.value.isClosed()
}

/**
 * Lock-free Multiply-Producer xxx-Consumer Queue core.
 * @see LockFreeTaskQueue
 */
internal class LockFreeTaskQueueCore<E : Any>(
    private val capacity: Int,
    private val singleConsumer: Boolean // true when there is only a single consumer (slightly faster)
) {
    private val mask = capacity - 1
    private val _next = atomic<Core<E>?>(null)
    private val _state = atomic(0L)
    private val array = atomicArrayOfNulls<Any?>(capacity)

    init {
        check(mask <= MAX_CAPACITY_MASK)
        check(capacity and mask == 0)
    }

    // Note: it is not atomic w.r.t. remove operation (remove can transiently fail when isEmpty is false)
    val isEmpty: Boolean get() = _state.value.withState { head, tail -> head == tail }
    val size: Int get() = _state.value.withState { head, tail -> (tail - head) and MAX_CAPACITY_MASK }

    fun close(): Boolean {
        _state.update { state ->
            if (state and CLOSED_MASK != 0L) return true // ok - already closed
            if (state and FROZEN_MASK != 0L) return false // frozen -- try next
            state or CLOSED_MASK // try set closed bit
        }
        return true
    }

    // ADD_CLOSED | ADD_FROZEN | ADD_SUCCESS
    fun addLast(element: E): Int {
        _state.loop { state ->
            if (state and (FROZEN_MASK or CLOSED_MASK) != 0L) return state.addFailReason() // cannot add
            state.withState { head, tail ->
                val mask = this.mask // manually move instance field to local for performance
                // If queue is Single-Consumer then there could be one element beyond head that we cannot overwrite,
                // so we check for full queue with an extra margin of one element
                if ((tail + 2) and mask == head and mask) return ADD_FROZEN // overfull, so do freeze & copy
                // If queue is Multi-Consumer then the consumer could still have not cleared element
                // despite the above check for one free slot.
                if (!singleConsumer && array[tail and mask].value != null) {
                    // There are two options in this situation
                    // 1. Spin-wait until consumer clears the slot
                    // 2. Freeze & resize to avoid spinning
                    // We use heuristic here to avoid memory-overallocation
                    // Freeze & reallocate when queue is small or more than half of the queue is used
                    if (capacity < MIN_ADD_SPIN_CAPACITY || (tail - head) and MAX_CAPACITY_MASK > capacity shr 1) {
                        return ADD_FROZEN
                    }
                    // otherwise spin
                    return@loop
                }
                val newTail = (tail + 1) and MAX_CAPACITY_MASK
                if (_state.compareAndSet(state, state.updateTail(newTail))) {
                    // successfully added
                    array[tail and mask].value = element
                    // could have been frozen & copied before this item was set -- correct it by filling placeholder
                    var cur = this
                    while(true) {
                        if (cur._state.value and FROZEN_MASK == 0L) break // all fine -- not frozen yet
                        cur = cur.next().fillPlaceholder(tail, element) ?: break
                    }
                    return ADD_SUCCESS // added successfully
                }
            }
        }
    }

    private fun fillPlaceholder(index: Int, element: E): Core<E>? {
        val old = array[index and mask].value
        /*
         * addLast actions:
         * 1) Commit tail slot
         * 2) Write element to array slot
         * 3) Check for array copy
         *
         * If copy happened between 2 and 3 then the consumer might have consumed our element,
         * then another producer might have written its placeholder in our slot, so we should
         * perform *unique* check that current placeholder is our to avoid overwriting another producer placeholder
         */
        if (old is Placeholder && old.index == index) {
            array[index and mask].value = element
            // we've corrected missing element, should check if that propagated to further copies, just in case
            return this
        }
        // it is Ok, no need for further action
        return null
    }

    // REMOVE_FROZEN | null (EMPTY) | E (SUCCESS)
    fun removeFirstOrNull(): Any? = removeFirstOrNullIf { true }

    // REMOVE_FROZEN | null (EMPTY) | E (SUCCESS)
    inline fun removeFirstOrNullIf(predicate: (E) -> Boolean): Any? {
        _state.loop { state ->
            if (state and FROZEN_MASK != 0L) return REMOVE_FROZEN // frozen -- cannot modify
            state.withState { head, tail ->
                if ((tail and mask) == (head and mask)) return null // empty
                val element = array[head and mask].value
                if (element == null) {
                    // If queue is Single-Consumer, then element == null only when add has not finished yet
                    if (singleConsumer) return null // consider it not added yet
                    // retry (spin) until consumer adds it
                    return@loop
                }
                // element == Placeholder can only be when add has not finished yet
                if (element is Placeholder) return null // consider it not added yet
                // now we tentative know element to remove -- check predicate
                @Suppress("UNCHECKED_CAST")
                if (!predicate(element as E)) return null
                // we cannot put null into array here, because copying thread could replace it with Placeholder and that is a disaster
                val newHead = (head + 1) and MAX_CAPACITY_MASK
                if (_state.compareAndSet(state, state.updateHead(newHead))) {
                    // Array could have been copied by another thread and it is perfectly fine, since only elements
                    // between head and tail were copied and there are no extra steps we should take here
                    array[head and mask].value = null // now can safely put null (state was updated)
                    return element // successfully removed in fast-path
                }
                // Multi-Consumer queue must retry this loop on CAS failure (another consumer might have removed element)
                if (!singleConsumer) return@loop
                // Single-consumer queue goes to slow-path for remove in case of interference
                var cur = this
                while (true) {
                    @Suppress("UNUSED_VALUE")
                    cur = cur.removeSlowPath(head, newHead) ?: return element
                }
            }
        }
    }

    private fun removeSlowPath(oldHead: Int, newHead: Int): Core<E>? {
        _state.loop { state ->
            state.withState { head, _ ->
                assert { head == oldHead } // "This queue can have only one consumer"
                if (state and FROZEN_MASK != 0L) {
                    // state was already frozen, so removed element was copied to next
                    return next() // continue to correct head in next
                }
                if (_state.compareAndSet(state, state.updateHead(newHead))) {
                    array[head and mask].value = null // now can safely put null (state was updated)
                    return null
                }
            }
        }
    }

    fun next(): LockFreeTaskQueueCore<E> = allocateOrGetNextCopy(markFrozen())

    private fun markFrozen(): Long =
        _state.updateAndGet { state ->
            if (state and FROZEN_MASK != 0L) return state // already marked
            state or FROZEN_MASK
        }

    private fun allocateOrGetNextCopy(state: Long): Core<E> {
        _next.loop { next ->
            if (next != null) return next // already allocated & copied
            _next.compareAndSet(null, allocateNextCopy(state))
        }
    }

    private fun allocateNextCopy(state: Long): Core<E> {
        val next = LockFreeTaskQueueCore<E>(capacity * 2, singleConsumer)
        state.withState { head, tail ->
            var index = head
            while (index and mask != tail and mask) {
                // replace nulls with placeholders on copy
                val value = array[index and mask].value ?: Placeholder(index)
                next.array[index and next.mask].value = value
                index++
            }
            next._state.value = state wo FROZEN_MASK
        }
        return next
    }

    // Used for validation in tests only
    fun <R> map(transform: (E) -> R): List<R> {
        val res = ArrayList<R>(capacity)
        _state.value.withState { head, tail ->
            var index = head
            while (index and mask != tail and mask) {
                // replace nulls with placeholders on copy
                val element = array[index and mask].value
                @Suppress("UNCHECKED_CAST")
                if (element != null && element !is Placeholder) res.add(transform(element as E))
                index++
            }
        }
        return res
    }

    // Used for validation in tests only
    fun isClosed(): Boolean = _state.value and CLOSED_MASK != 0L


    // Instance of this class is placed into array when we have to copy array, but addLast is in progress --
    // it had already reserved a slot in the array (with null) and have not yet put its value there.
    // Placeholder keeps the actual index (not masked) to distinguish placeholders on different wraparounds of array
    // Internal because of inlining
    internal class Placeholder(@JvmField val index: Int)

    @Suppress("PrivatePropertyName", "MemberVisibilityCanBePrivate")
    internal companion object {
        const val INITIAL_CAPACITY = 8

        const val CAPACITY_BITS = 30
        const val MAX_CAPACITY_MASK = (1 shl CAPACITY_BITS) - 1
        const val HEAD_SHIFT = 0
        const val HEAD_MASK = MAX_CAPACITY_MASK.toLong() shl HEAD_SHIFT
        const val TAIL_SHIFT = HEAD_SHIFT + CAPACITY_BITS
        const val TAIL_MASK = MAX_CAPACITY_MASK.toLong() shl TAIL_SHIFT

        const val FROZEN_SHIFT = TAIL_SHIFT + CAPACITY_BITS
        const val FROZEN_MASK = 1L shl FROZEN_SHIFT
        const val CLOSED_SHIFT = FROZEN_SHIFT + 1
        const val CLOSED_MASK = 1L shl CLOSED_SHIFT

        const val MIN_ADD_SPIN_CAPACITY = 1024

        @JvmField val REMOVE_FROZEN = Symbol("REMOVE_FROZEN")

        const val ADD_SUCCESS = 0
        const val ADD_FROZEN = 1
        const val ADD_CLOSED = 2

        infix fun Long.wo(other: Long) = this and other.inv()
        fun Long.updateHead(newHead: Int) = (this wo HEAD_MASK) or (newHead.toLong() shl HEAD_SHIFT)
        fun Long.updateTail(newTail: Int) = (this wo TAIL_MASK) or (newTail.toLong() shl TAIL_SHIFT)

        inline fun <T> Long.withState(block: (head: Int, tail: Int) -> T): T {
            val head = ((this and HEAD_MASK) shr HEAD_SHIFT).toInt()
            val tail = ((this and TAIL_MASK) shr TAIL_SHIFT).toInt()
            return block(head, tail)
        }

        // FROZEN | CLOSED
        fun Long.addFailReason(): Int = if (this and CLOSED_MASK != 0L) ADD_CLOSED else ADD_FROZEN
    }
}