/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental.internal

import kotlinx.atomicfu.*
import java.util.concurrent.atomic.*

private typealias Core<E> = LockFreeMPSCQueueCore<E>

/**
 * @suppress **This is unstable API and it is subject to change.**
 */
internal class LockFreeMPSCQueue<E : Any> {
    private val _cur = atomic(Core<E>(Core.INITIAL_CAPACITY))

    // Note: it is not atomic w.r.t. remove operation (remove can transiently fail when isEmpty is false)
    val isEmpty: Boolean get() = _cur.value.isEmpty

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
    fun removeFirstOrNull(): E? {
        _cur.loop { cur ->
            val result = cur.removeFirstOrNull()
            if (result !== Core.REMOVE_FROZEN) return result as E?
            _cur.compareAndSet(cur, cur.next())
        }
    }
}

/**
 * @suppress **This is unstable API and it is subject to change.**
 */
internal class LockFreeMPSCQueueCore<E : Any>(private val capacity: Int) {
    private val mask = capacity - 1
    private val _next = atomic<Core<E>?>(null)
    private val _state = atomic(0L)
    private val array = AtomicReferenceArray<Any?>(capacity);

    init {
        check(mask <= MAX_CAPACITY_MASK)
        check(capacity and mask == 0)
    }

    // Note: it is not atomic w.r.t. remove operation (remove can transiently fail when isEmpty is false)
    val isEmpty: Boolean get() = _state.value.withState { head, tail -> head == tail }

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
                // there could be one REMOVE element beyond head that we cannot stump up,
                // so we check for full queue with an extra margin of one element
                if ((tail + 2) and mask == head and mask) return ADD_FROZEN // overfull, so do freeze & copy
                val newTail = (tail + 1) and MAX_CAPACITY_MASK
                if (_state.compareAndSet(state, state.updateTail(newTail))) {
                    // successfully added
                    array[tail and mask] = element
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
        if (array.compareAndSet(index and mask, PLACEHOLDER, element)) {
            // we've corrected missing element, should check if that propagated to further copies, just in case
            return this
        }
        // it is Ok, no need for further action
        return null
    }

    // SINGLE CONSUMER
    // REMOVE_FROZEN | null (EMPTY) | E (SUCCESS)
    fun removeFirstOrNull(): Any? {
        _state.loop { state ->
            if (state and FROZEN_MASK != 0L) return REMOVE_FROZEN // frozen -- cannot modify
            state.withState { head, tail ->
                if ((tail and mask) == (head and mask)) return null // empty
                // because queue is Single Consumer, then element == null|PLACEHOLDER can only be when add has not finished yet
                val element = array[head and mask] ?: return null
                if (element === PLACEHOLDER) return null // same story -- consider it not added yet
                check(element !== REMOVED) { "This queue can have only one consumer" }
                // tentatively remove element to let GC work
                // we cannot put null into array, because copying thread could replace it with PLACEHOLDER
                // and that is a disaster, so a separate REMOVED token is used here.
                // Note: at most one REMOVED in the array, because single consumer.
                array[head and mask] = REMOVED
                val newHead = (head + 1) and MAX_CAPACITY_MASK
                if (_state.compareAndSet(state, state.updateHead(newHead))) {
                    array[head and mask] = null // now can safely put null (state was updated)
                    return element // successfully removed in fast-path
                }
                // Slow-path for remove in case of interference
                var cur = this
                while (true) {
                    cur = cur.removeSlowPath(head, newHead) ?: return element
                }
            }
        }
    }

    private fun removeSlowPath(oldHead: Int, newHead: Int): Core<E>? {
        _state.loop { state ->
            state.withState { head, _ ->
                check(head == oldHead) { "This queue can have only one consumer" }
                if (state and FROZEN_MASK != 0L) {
                    // state was already frozen, so either old or REMOVED item could have been copied to next
                    val next = next()
                    next.array[head and next.mask] = REMOVED // make sure it is removed in new array regardless
                    return next // continue to correct head in next
                }
                if (_state.compareAndSet(state, state.updateHead(newHead))) {
                    array[head and mask] = null // now can safely put null (state was updated)
                    return null
                }
            }
        }
    }

    fun next(): LockFreeMPSCQueueCore<E> = allocateOrGetNextCopy(markFrozen())

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
        val next = LockFreeMPSCQueueCore<E>(capacity * 2)
        state.withState { head, tail ->
            var index = head
            while (index and mask != tail and mask) {
                // replace nulls with placeholders on copy
                next.array[index and next.mask] = array[index and mask] ?: PLACEHOLDER
                index++
            }
            next._state.value = state wo FROZEN_MASK
        }
        return next
    }

    @Suppress("PrivatePropertyName")
    internal companion object {
        internal const val INITIAL_CAPACITY = 8

        private const val CAPACITY_BITS = 30
        private const val MAX_CAPACITY_MASK = (1 shl CAPACITY_BITS) - 1
        private const val HEAD_SHIFT = 0
        private const val HEAD_MASK = MAX_CAPACITY_MASK.toLong() shl HEAD_SHIFT
        private const val TAIL_SHIFT = HEAD_SHIFT + CAPACITY_BITS
        private const val TAIL_MASK = MAX_CAPACITY_MASK.toLong() shl TAIL_SHIFT

        private const val FROZEN_SHIFT = TAIL_SHIFT + CAPACITY_BITS
        private const val FROZEN_MASK = 1L shl FROZEN_SHIFT
        private const val CLOSED_SHIFT = FROZEN_SHIFT + 1
        private const val CLOSED_MASK = 1L shl CLOSED_SHIFT

        @JvmField internal val REMOVE_FROZEN = Symbol("REMOVE_FROZEN")

        internal const val ADD_SUCCESS = 0
        internal const val ADD_FROZEN = 1
        internal const val ADD_CLOSED = 2

        private val PLACEHOLDER = Symbol("PLACEHOLDER")
        private val REMOVED = Symbol("PLACEHOLDER")

        private infix fun Long.wo(other: Long) = this and other.inv()
        private fun Long.updateHead(newHead: Int) = (this wo HEAD_MASK) or (newHead.toLong() shl HEAD_SHIFT)
        private fun Long.updateTail(newTail: Int) = (this wo TAIL_MASK) or (newTail.toLong() shl TAIL_SHIFT)

        private inline fun <T> Long.withState(block: (head: Int, tail: Int) -> T): T {
            val head = ((this and HEAD_MASK) shr HEAD_SHIFT).toInt()
            val tail = ((this and TAIL_MASK) shr TAIL_SHIFT).toInt()
            return block(head, tail)
        }

        // FROZEN | CLOSED
        private fun Long.addFailReason(): Int = if (this and CLOSED_MASK != 0L) ADD_CLOSED else ADD_FROZEN
    }
}