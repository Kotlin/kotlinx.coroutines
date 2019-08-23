/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

private typealias Node = LinkedListNode

/** @suppress **This is unstable API and it is subject to change.** */
@Suppress("NO_ACTUAL_CLASS_MEMBER_FOR_EXPECTED_CLASS") // :TODO: Remove when fixed: https://youtrack.jetbrains.com/issue/KT-23703
public actual typealias LockFreeLinkedListNode = LinkedListNode

/** @suppress **This is unstable API and it is subject to change.** */
public actual typealias LockFreeLinkedListHead = LinkedListHead

/** @suppress **This is unstable API and it is subject to change.** */
public open class LinkedListNode {
    @PublishedApi internal var _next = this
    @PublishedApi internal var _prev = this
    @PublishedApi internal var _removed: Boolean = false

    public inline val nextNode get() = _next
    public inline val prevNode get() = _prev
    public inline val isRemoved get() = _removed

    public fun addLast(node: Node) {
        val prev = this._prev
        node._next = this
        node._prev = prev
        prev._next = node
        this._prev = node
    }

    public open fun remove(): Boolean {
        if (_removed) return false
        val prev = this._prev
        val next = this._next
        prev._next = next
        next._prev = prev
        _removed = true
        return true
    }

    public fun addOneIfEmpty(node: Node): Boolean {
        if (_next !== this) return false
        addLast(node)
        return true
    }

    public inline fun addLastIf(node: Node, crossinline condition: () -> Boolean): Boolean {
        if (!condition()) return false
        addLast(node)
        return true
    }

    public inline fun addLastIfPrev(node: Node, predicate: (Node) -> Boolean): Boolean {
        if (!predicate(_prev)) return false
        addLast(node)
        return true
    }

    public inline fun addLastIfPrevAndIf(
        node: Node,
        predicate: (Node) -> Boolean, // prev node predicate
        crossinline condition: () -> Boolean // atomically checked condition
    ): Boolean {
        if (!predicate(_prev)) return false
        if (!condition()) return false
        addLast(node)
        return true
    }

    public fun helpRemove() {} // no-op without multithreading

    public fun removeFirstOrNull(): Node? {
        val next = _next
        if (next === this) return null
        check(next.remove()) { "Should remove" }
        return next
    }

    public inline fun <reified T> removeFirstIfIsInstanceOfOrPeekIf(predicate: (T) -> Boolean): T? {
        val next = _next
        if (next === this) return null
        if (next !is T) return null
        if (predicate(next)) return next
        check(next.remove()) { "Should remove" }
        return next
    }
}

/** @suppress **This is unstable API and it is subject to change.** */
public actual open class AddLastDesc<T : Node> actual constructor(
    actual val queue: Node,
    actual val node: T
) : AbstractAtomicDesc() {
    protected override val affectedNode: Node get() = queue._prev
    protected actual override fun onPrepare(affected: Node, next: Node): Any? = null
    protected override fun onComplete() = queue.addLast(node)
    protected actual override fun finishOnSuccess(affected: LockFreeLinkedListNode, next: LockFreeLinkedListNode) = Unit
}

/** @suppress **This is unstable API and it is subject to change.** */
public actual open class RemoveFirstDesc<T> actual constructor(
    actual val queue: LockFreeLinkedListNode
) : AbstractAtomicDesc() {

    @Suppress("UNCHECKED_CAST")
    public actual val result: T get() = affectedNode as T
    protected override val affectedNode: Node = queue.nextNode
    protected actual open fun validatePrepared(node: T): Boolean = true
    protected actual final override fun onPrepare(affected: LockFreeLinkedListNode, next: LockFreeLinkedListNode): Any? {
        @Suppress("UNCHECKED_CAST")
        validatePrepared(affectedNode as T)
        return null
    }
    protected override fun onComplete() { queue.removeFirstOrNull() }
    protected actual override fun finishOnSuccess(affected: LockFreeLinkedListNode, next: LockFreeLinkedListNode) = Unit
}

/** @suppress **This is unstable API and it is subject to change.** */
public actual abstract class AbstractAtomicDesc : AtomicDesc() {
    protected abstract val affectedNode: Node
    protected actual abstract fun onPrepare(affected: Node, next: Node): Any?
    protected abstract fun onComplete()

    actual final override fun prepare(op: AtomicOp<*>): Any? {
        val affected = affectedNode
        val next = affected._next
        val failure = failure(affected)
        if (failure != null) return failure
        return onPrepare(affected, next)
    }

    actual final override fun complete(op: AtomicOp<*>, failure: Any?) = onComplete()
    protected actual open fun failure(affected: LockFreeLinkedListNode): Any? = null // Never fails by default
    protected actual open fun retry(affected: LockFreeLinkedListNode, next: Any): Boolean = false // Always succeeds
    protected actual abstract fun finishOnSuccess(affected: LockFreeLinkedListNode, next: LockFreeLinkedListNode)
}

/** @suppress **This is unstable API and it is subject to change.** */
public open class LinkedListHead : LinkedListNode() {
    public val isEmpty get() = _next === this

    /**
     * Iterates over all elements in this list of a specified type.
     */
    public inline fun <reified T : Node> forEach(block: (T) -> Unit) {
        var cur: Node = _next
        while (cur != this) {
            if (cur is T) block(cur)
            cur = cur._next
        }
    }

    // just a defensive programming -- makes sure that list head sentinel is never removed
    public final override fun remove(): Boolean = throw UnsupportedOperationException()
}
