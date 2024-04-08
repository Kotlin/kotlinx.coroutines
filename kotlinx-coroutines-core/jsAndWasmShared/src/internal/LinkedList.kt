@file:Suppress("unused", "NO_EXPLICIT_RETURN_TYPE_IN_API_MODE", "NO_EXPLICIT_VISIBILITY_IN_API_MODE")

package kotlinx.coroutines.internal

private typealias Node = LinkedListNode

/** @suppress **This is unstable API and it is subject to change.** */
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

    /*
     * Remove that is invoked as a virtual function with a
     * potentially augmented behaviour.
     * I.g. `LockFreeLinkedListHead` throws, while `SendElementWithUndeliveredHandler`
     * invokes handler on remove
     */
    public open fun remove(): Boolean {
        return removeImpl()
    }

    @PublishedApi
    internal fun removeImpl(): Boolean {
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

    public fun helpRemove() {} // No concurrency on JS -> no removal

    public fun removeFirstOrNull(): Node? {
        val next = _next
        if (next === this) return null
        check(next.removeImpl()) { "Should remove" }
        return next
    }
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
    public final override fun remove(): Nothing = throw UnsupportedOperationException()
}
