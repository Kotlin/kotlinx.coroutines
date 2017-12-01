package kotlinx.coroutines.experimental.internal

private typealias Node = LinkedListNode

public open class LinkedListNode {
    public var next = this
        private set
    public var prev = this
        private set
    public var isRemoved: Boolean = false
        private set

    public fun addLast(node: Node) {
        val prev = this.prev
        node.next = this
        node.prev = prev
        prev.next = node
        this.prev = node
    }

    public open fun remove() {
        val prev = this.prev
        val next = this.next
        prev.next = next
        next.prev = prev
        isRemoved = true
    }
}

public open class LinkedListHead : LinkedListNode() {
    /**
     * Iterates over all elements in this list of a specified type.
     */
    public inline fun <reified T : Node> forEach(block: (T) -> Unit) {
        var cur: Node = next
        while (cur != this) {
            if (cur is T) block(cur)
            cur = cur.next
        }
    }

    // just a defensive programming -- makes sure that list head sentinel is never removed
    public final override fun remove() = throw UnsupportedOperationException()
}

