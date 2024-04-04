@file:Suppress("unused", "NO_EXPLICIT_RETURN_TYPE_IN_API_MODE", "NO_EXPLICIT_VISIBILITY_IN_API_MODE")

package kotlinx.coroutines.internal

private typealias Node = LockFreeLinkedListNode

/** @suppress **This is unstable API and it is subject to change.** */
public actual open class LockFreeLinkedListNode {
    @PublishedApi internal var _next = this
    @PublishedApi internal var _prev = this
    @PublishedApi internal var _removed: Boolean = false

    public actual inline val nextNode get() = _next
    inline actual val prevNode get() = _prev
    inline actual val isRemoved get() = _removed

    @PublishedApi
    internal fun addLast(node: Node) {
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
    public actual open fun remove(): Boolean {
        return removeImpl()
    }

    private fun removeImpl(): Boolean {
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
        addLast(node)
        return true
    }

    public actual inline fun addLastIf(node: Node, crossinline condition: () -> Boolean): Boolean {
        if (!condition()) return false
        addLast(node)
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
