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
        val failure = failure(affected, next)
        if (failure != null) return failure
        return onPrepare(affected, next)
    }

    actual final override fun complete(op: AtomicOp<*>, failure: Any?) = onComplete()
    protected actual open fun failure(affected: LockFreeLinkedListNode, next: Any): Any? = null // Never fails by default
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
    public final override fun remove() = throw UnsupportedOperationException()
}
