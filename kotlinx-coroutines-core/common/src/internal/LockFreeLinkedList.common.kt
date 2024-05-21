@file:Suppress("NO_EXPLICIT_VISIBILITY_IN_API_MODE")

package kotlinx.coroutines.internal

/** @suppress **This is unstable API and it is subject to change.** */
public expect open class LockFreeLinkedListNode() {
    public val isRemoved: Boolean
    public val nextNode: LockFreeLinkedListNode
    public val prevNode: LockFreeLinkedListNode
    public fun addLast(node: LockFreeLinkedListNode, permissionsBitmask: Int): Boolean
    public fun addOneIfEmpty(node: LockFreeLinkedListNode): Boolean
    public open fun remove(): Boolean

    /**
     * Closes the list for anything that requests the permission [forbiddenElementsBit].
     * Only a single permission can be forbidden at a time, but this isn't checked.
     */
    public fun close(forbiddenElementsBit: Int)
}

/** @suppress **This is unstable API and it is subject to change.** */
public expect open class LockFreeLinkedListHead() : LockFreeLinkedListNode {
    public inline fun forEach(block: (LockFreeLinkedListNode) -> Unit)
    public final override fun remove(): Nothing
}
