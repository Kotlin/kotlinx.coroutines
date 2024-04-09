@file:Suppress("NO_EXPLICIT_VISIBILITY_IN_API_MODE")

package kotlinx.coroutines.internal

/** @suppress **This is unstable API and it is subject to change.** */
public expect open class LockFreeLinkedListNode() {
    /**
     * Try putting `node` into a list.
     *
     * Returns:
     * - The new head of the list if the operation succeeded.
     * - The head of the list if someone else concurrently added this node to the list,
     *   but no other modifications to the list were made.
     * - Some garbage if the list was already edited.
     */
    public fun attachToList(node: LockFreeLinkedListHead): LockFreeLinkedListNode

    /**
     * Remove this node from the list.
     */
    public open fun remove()
}

/** @suppress **This is unstable API and it is subject to change.** */
public expect open class LockFreeLinkedListHead() {
    /**
     * Iterates over all non-removed elements in this list, skipping every node until (and including) [startAfter].
     */
    public inline fun forEach(startAfter: LockFreeLinkedListNode? = null, block: (LockFreeLinkedListNode) -> Unit)

    /**
     * Closes the list for anything that requests the permission [forbiddenElementsBit].
     * Only a single permission can be forbidden at a time, but this isn't checked.
     */
    public fun close(forbiddenElementsBit: Int)

    /**
     * Adds the [node] to the end of the list if every bit in [permissionsBitmask] is still allowed in the list.
     */
    public fun addLast(node: LockFreeLinkedListNode, permissionsBitmask: Int): Boolean
}
