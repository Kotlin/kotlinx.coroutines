package kotlinx.coroutines.internal

private typealias Node = LockFreeLinkedListNode

/** @suppress **This is unstable API and it is subject to change.** */
public actual open class LockFreeLinkedListNode {
    @PublishedApi internal var _next: LockFreeLinkedListNode = this
    @PublishedApi internal var _prev: LockFreeLinkedListNode = this
    @PublishedApi internal var _removed: Boolean = false

    public actual inline val nextNode: LockFreeLinkedListNode get() = _next
    public actual inline val prevNode: LockFreeLinkedListNode get() = _prev
    public actual inline val isRemoved: Boolean get() = _removed

    public actual fun addLast(node: Node, permissionsBitmask: Int): Boolean = when (val prev = this._prev) {
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

    public actual fun close(forbiddenElementsBit: Int) {
        val _ = addLast(ListClosed(forbiddenElementsBit), forbiddenElementsBit)
    }

    /*
     * Remove that is invoked as a virtual function with a
     * potentially augmented behaviour.
     * I.g. `LockFreeLinkedListHead` throws, while `SendElementWithUndeliveredHandler`
     * invokes handler on remove
     */
    @IgnorableReturnValue
    public actual open fun remove(): Boolean {
        if (_removed) return false
        val prev = this._prev
        val next = this._next
        prev._next = next
        next._prev = prev
        _removed = true
        return true
    }

    public actual fun addOneIfEmpty(node: Node): Boolean {
        if (_next !== this) return false
        val _ = addLast(node, Int.MIN_VALUE)
        return true
    }
}

/** @suppress **This is unstable API and it is subject to change.** */
public actual open class LockFreeLinkedListHead : Node() {
    /**
     * Iterates over all elements in this list of a specified type.
     */
    public actual inline fun forEach(block: (Node) -> Unit) {
        var cur: Node = _next
        while (cur != this) {
            block(cur)
            cur = cur._next
        }
    }

    // just a defensive programming -- makes sure that list head sentinel is never removed
    public actual final override fun remove(): Nothing = throw UnsupportedOperationException()
}

private class ListClosed(val forbiddenElementsBitmask: Int): LockFreeLinkedListNode()
