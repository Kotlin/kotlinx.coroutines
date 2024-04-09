@file:Suppress("unused", "NO_EXPLICIT_RETURN_TYPE_IN_API_MODE", "NO_EXPLICIT_VISIBILITY_IN_API_MODE")

package kotlinx.coroutines.internal

import kotlinx.coroutines.*

private typealias Node = LockFreeLinkedListNode

/** @suppress **This is unstable API and it is subject to change.** */
public actual open class LockFreeLinkedListNode {
    @PublishedApi internal var _next = this
    @PublishedApi internal var _prev = this
    @PublishedApi internal var _removed: Boolean = false

    fun addLast(node: Node, permissionsBitmask: Int): Boolean = when (val prev = this._prev) {
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

    /*
     * Remove that is invoked as a virtual function with a
     * potentially augmented behaviour.
     * I.g. `LockFreeLinkedListHead` throws, while `SendElementWithUndeliveredHandler`
     * invokes handler on remove
     */
    public actual open fun remove() {
        if (_removed) return
        val prev = this._prev
        val next = this._next
        prev._next = next
        next._prev = prev
        _removed = true
    }

    public actual fun attachToList(node: LockFreeLinkedListHead): Node {
        if (_next !== this) return _next
        val success = addLast(node, Int.MIN_VALUE)
        assert { success }
        return node
    }
}

/** @suppress **This is unstable API and it is subject to change.** */
public actual open class LockFreeLinkedListHead : Node() {
    /**
     * Iterates over all elements in this list of a specified type.
     */
    public actual inline fun forEach(startAfter: LockFreeLinkedListNode?, block: (Node) -> Unit) {
        var cur: Node = startAfter ?: this
        while (cur._removed) cur = cur._prev // rollback to prev non-removed (or list head)
        cur = cur._next
        while (cur !== this) {
            if (!cur._removed) {
                block(cur)
            }
            cur = cur._next
        }
    }

    public actual fun close(forbiddenElementsBit: Int) {
        addLast(ListClosed(forbiddenElementsBit), forbiddenElementsBit)
    }

    // just a defensive programming -- makes sure that list head sentinel is never removed
    public final override fun remove(): Nothing = throw UnsupportedOperationException()
}

private class ListClosed(val forbiddenElementsBitmask: Int): LockFreeLinkedListNode()
