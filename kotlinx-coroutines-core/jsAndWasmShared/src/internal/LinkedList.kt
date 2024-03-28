@file:Suppress("unused", "NO_EXPLICIT_RETURN_TYPE_IN_API_MODE", "NO_EXPLICIT_VISIBILITY_IN_API_MODE")

package kotlinx.coroutines.internal

import kotlinx.coroutines.*

private typealias Node = LinkedListNode

/** @suppress **This is unstable API and it is subject to change.** */
public actual typealias LockFreeLinkedListNode = LinkedListNode

/** @suppress **This is unstable API and it is subject to change.** */
public actual typealias LockFreeLinkedListHead = LinkedListHead

/** @suppress **This is unstable API and it is subject to change.** */
public open class LinkedListNode : DisposableHandle {
    @PublishedApi internal var _next = this
    @PublishedApi internal var _prev = this
    @PublishedApi internal var _removed: Boolean = false

    public inline val nextNode get() = _next
    public inline val prevNode get() = _prev
    public inline val isRemoved get() = _removed

    public fun addLast(node: Node, permissionsBitmask: Int): Boolean = when (val prev = this._prev) {
        is ListClosed ->
            prev.forbiddenElementsBitmask and permissionsBitmask == 0 && prev.addLast(node, permissionsBitmask)
        else -> {
            node._next = this
            node._prev = prev
            prev._next = node
            this._prev = node
            true
        }
    }

    public fun close(forbiddenElementsBit: Int) {
        addLast(ListClosed(forbiddenElementsBit), forbiddenElementsBit)
    }

    /*
     * Remove that is invoked as a virtual function with a
     * potentially augmented behaviour.
     * I.g. `LockFreeLinkedListHead` throws, while `SendElementWithUndeliveredHandler`
     * invokes handler on remove
     */
    public open fun remove(): Boolean {
        if (_removed) return false
        val prev = this._prev
        val next = this._next
        prev._next = next
        next._prev = prev
        _removed = true
        return true
    }

    override fun dispose() {
        remove()
    }

    public fun addOneIfEmpty(node: Node): Boolean {
        if (_next !== this) return false
        addLast(node, Int.MIN_VALUE)
        return true
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

private class ListClosed(val forbiddenElementsBitmask: Int): LinkedListNode()
