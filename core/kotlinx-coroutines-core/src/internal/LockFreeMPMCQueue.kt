/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package internal

import kotlinx.atomicfu.*

internal open class LockFreeMPMCQueueNode<T> {
    val next = atomic<T?>(null)

    @PublishedApi internal val nextValue: T? get() = next.value
}

/*
 * Michael & Scott lock-free Multi-Producer Multi-Consumer Queue with support for poll with predicate.
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
internal open class LockFreeMPMCQueue<T : LockFreeMPMCQueueNode<T>> {
    private val head =
        @Suppress("UNCHECKED_CAST")
        atomic(LockFreeMPMCQueueNode<T>() as T) // sentinel

    private val tail = atomic(head.value)
    internal val headValue: T get() = head.value

    public fun addLast(node: T): Boolean {
        tail.loop { curTail ->
            val curNext = curTail.next.value
            if (curNext != null) {
                tail.compareAndSet(curTail, curNext)
                return@loop // retry
            }
            if (curTail.next.compareAndSet(null, node)) {
                tail.compareAndSet(curTail, node)
                return true
            }
        }
    }

    public fun removeFirstOrNull(): T? {
        head.loop { curHead ->
            val next = curHead.next.value ?: return null
            if (head.compareAndSet(curHead, next)) {
                return next
            }
        }
    }

    fun headCas(curHead: T, update: T) = head.compareAndSet(curHead, update)

    public inline fun removeFirstOrNullIf(predicate: (T) -> Boolean): T? {
        while (true) {
            val curHead = headValue
            val next = curHead.nextValue ?: return null
            if (!predicate(next)) return null
            if (headCas(curHead, next)) {
                return next
            }
        }
    }

    public fun isEmpty(): Boolean = size == 0

    public val size: Int get() = fold(0) { acc, _ -> acc + 1 }

    public inline fun <R> fold(initial: R, operation: (acc: R, T) -> R): R {
        var acc = initial
        var cur = headValue
        while (true) {
            val next = cur.nextValue ?: break
            acc = operation(acc, next)
            cur = next
        }
        return acc
    }
}
