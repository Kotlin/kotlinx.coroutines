@file:Suppress("NO_EXPLICIT_VISIBILITY_IN_API_MODE")

package kotlinx.coroutines.internal

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlin.jvm.*

private typealias Node = LockFreeLinkedListNode

/**
 * Doubly-linked concurrent list node with remove support.
 * Based on paper
 * ["Lock-Free and Practical Doubly Linked List-Based Deques Using Single-Word Compare-and-Swap"](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.140.4693&rep=rep1&type=pdf)
 * by Sundell and Tsigas with considerable changes.
 *
 * The core idea of the algorithm is to maintain a doubly-linked list with an ever-present sentinel node (it is
 * never removed) that serves both as a list head and tail and to linearize all operations (both insert and remove) on
 * the update of the next pointer. Removed nodes have their next pointer marked with [Removed] class.
 *
 * Important notes:
 * - There are no operations to add items to left side of the list, only to the end (right side), because we cannot
 *   efficiently linearize them with atomic multi-step head-removal operations. In short,
 *   support for [describeRemoveFirst] operation precludes ability to add items at the beginning.
 * - Previous pointers are not marked for removal. We don't support linearizable backwards traversal.
 * - Remove-helping logic is simplified and consolidated in [correctPrev] method.
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
@Suppress("LeakingThis")
@InternalCoroutinesApi
public actual open class LockFreeLinkedListNode {
    private val _next = atomic<Any>(this) // Node | Removed | OpDescriptor
    private val _prev = atomic(this) // Node to the left (cannot be marked as removed)
    private val _removedRef = atomic<Removed?>(null) // lazily cached removed ref to this

    private fun removed(): Removed =
        _removedRef.value ?: Removed(this).also { _removedRef.lazySet(it) }

    public open val isRemoved: Boolean get() = next is Removed

    // LINEARIZABLE. Returns Node | Removed
    public val next: Any get() = _next.value

    // LINEARIZABLE. Returns next non-removed Node
    val nextNode: Node get() =
        next.let { (it as? Removed)?.ref ?: it as Node } // unwraps the `next` node

    // LINEARIZABLE WHEN THIS NODE IS NOT REMOVED:
    // Returns prev non-removed Node, makes sure prev is correct (prev.next === this)
    // NOTE: if this node is removed, then returns non-removed previous node without applying
    // prev.next correction, which does not provide linearizable backwards iteration, but can be used to
    // resume forward iteration when current node was removed.
    public val prevNode: Node
        get() = correctPrev() ?: findPrevNonRemoved(_prev.value)

    private tailrec fun findPrevNonRemoved(current: Node): Node {
        if (!current.isRemoved) return current
        return findPrevNonRemoved(current._prev.value)
    }

    // ------ addOneIfEmpty ------

    public actual fun attachToList(node: LockFreeLinkedListHead): Node {
        (node as Node)._prev.lazySet(this)
        (node as Node)._next.lazySet(this)
        while (true) {
            val next = next
            if (next !== this) return nextNode // this is not an empty list!
            if (_next.compareAndSet(this, node)) {
                // added successfully (linearized add) -- fixup the list
                (node as Node).finishAdd(this)
                return node
            }
        }
    }

    // ------ addLastXXX ------

    /**
     * Adds last item to this list. Returns `false` if the list is closed.
     */
    fun addLast(node: Node, permissionsBitmask: Int): Boolean {
        while (true) { // lock-free loop on prev.next
            val currentPrev = prevNode
            return when {
                currentPrev is ListClosed ->
                    currentPrev.forbiddenElementsBitmask and permissionsBitmask == 0 &&
                        currentPrev.addLast(node, permissionsBitmask)
                currentPrev.addNext(node, this) -> true
                else -> continue
            }
        }
    }

    /**
     * Given:
     * ```
     *                +-----------------------+
     *          this  |         node          V  next
     *          +---+---+     +---+---+     +---+---+
     *  ... <-- | P | N |     | P | N |     | P | N | --> ....
     *          +---+---+     +---+---+     +---+---+
     *                ^                       |
     *                +-----------------------+
     * ```
     * Produces:
     * ```
     *          this            node             next
     *          +---+---+     +---+---+     +---+---+
     *  ... <-- | P | N | ==> | P | N | --> | P | N | --> ....
     *          +---+---+     +---+---+     +---+---+
     *                ^         |   ^         |
     *                +---------+   +---------+
     * ```
     *  Where `==>` denotes linearization point.
     *  Returns `false` if `next` was not following `this` node.
     */
    @PublishedApi
    internal fun addNext(node: Node, next: Node): Boolean {
        node._prev.lazySet(this)
        node._next.lazySet(next)
        if (!_next.compareAndSet(next, node)) return false
        // added successfully (linearized add) -- fixup the list
        node.finishAdd(next)
        return true
    }

    // ------ removeXXX ------

    /**
     * Removes this node from the list. Returns `true` when removed successfully, or `false` if the node was already
     * removed or if it was not added to any list in the first place.
     *
     * **Note**: Invocation of this operation does not guarantee that remove was actually complete if result was `false`.
     * In particular, invoking [nextNode].[prevNode] might still return this node even though it is "already removed".
     */
    public actual open fun remove() {
        removeOrNext()
    }

    // returns null if removed successfully or next node if this node is already removed
    @PublishedApi
    internal fun removeOrNext(): Node? {
        while (true) { // lock-free loop on next
            val next = this.next
            if (next is Removed) return next.ref // was already removed -- don't try to help (original thread will take care)
            if (next === this) return next // was not even added
            val removed = (next as Node).removed()
            if (_next.compareAndSet(next, removed)) {
                // was removed successfully (linearized remove) -- fixup the list
                next.correctPrev()
                return null
            }
        }
    }

    // This is Harris's RDCSS (Restricted Double-Compare Single Swap) operation
    // It inserts "op" descriptor of when "op" status is still undecided (rolls back otherwise)


    // ------ other helpers ------

    /**
     * Given:
     * ```
     *
     *          prev            this             next
     *          +---+---+     +---+---+     +---+---+
     *  ... <-- | P | N | --> | P | N | --> | P | N | --> ....
     *          +---+---+     +---+---+     +---+---+
     *              ^ ^         |             |
     *              | +---------+             |
     *              +-------------------------+
     * ```
     * Produces:
     * ```
     *          prev            this             next
     *          +---+---+     +---+---+     +---+---+
     *  ... <-- | P | N | --> | P | N | --> | P | N | --> ....
     *          +---+---+     +---+---+     +---+---+
     *                ^         |   ^         |
     *                +---------+   +---------+
     * ```
     */
    private fun finishAdd(next: Node) {
        next._prev.loop { nextPrev ->
            if (this.next !== next) return // this or next was removed or another node added, remover/adder fixes up links
            if (next._prev.compareAndSet(nextPrev, this)) {
                // This newly added node could have been removed, and the above CAS would have added it physically again.
                // Let us double-check for this situation and correct if needed
                if (isRemoved) next.correctPrev()
                return
            }
        }
    }

    /**
     * Returns the corrected value of the previous node while also correcting the `prev` pointer
     * (so that `this.prev.next === this`) and helps complete node removals to the left ot this node.
     *
     * It returns `null` in two special cases:
     *
     * - When this node is removed. In this case there is no need to waste time on corrections, because
     *   remover of this node will ultimately call [correctPrev] on the next node and that will fix all
     *   the links from this node, too.
     */
    private tailrec fun correctPrev(): Node? {
        val oldPrev = _prev.value
        var prev: Node = oldPrev
        var last: Node? = null // will be set so that last.next === prev
        while (true) { // move the left until first non-removed node
            val prevNext: Any = prev._next.value
            when {
                // fast path to find quickly find prev node when everything is properly linked
                prevNext === this -> {
                    if (oldPrev === prev) return prev // nothing to update -- all is fine, prev found
                    // otherwise need to update prev
                    if (!this._prev.compareAndSet(oldPrev, prev)) {
                        // Note: retry from scratch on failure to update prev
                        return correctPrev()
                    }
                    return prev // return the correct prev
                }
                // slow path when we need to help remove operations
                this.isRemoved -> return null // nothing to do, this node was removed, bail out asap to save time
                prevNext is Removed -> {
                    if (last !== null) {
                        // newly added (prev) node is already removed, correct last.next around it
                        if (!last._next.compareAndSet(prev, prevNext.ref)) {
                            return correctPrev() // retry from scratch on failure to update next
                        }
                        prev = last
                        last = null
                    } else {
                        prev = prev._prev.value
                    }
                }
                else -> { // prevNext is a regular node, but not this -- help delete
                    last = prev
                    prev = prevNext as Node
                }
            }
        }
    }

    internal fun validateNode(prev: Node, next: Node) {
        assert { prev === this._prev.value }
        assert { next === this._next.value }
    }

    override fun toString(): String = "${this::classSimpleName}@${this.hexAddress}"
}

private class Removed(@JvmField val ref: Node) {
    override fun toString(): String = "Removed[$ref]"
}

/**
 * Head (sentinel) item of the linked list that is never removed.
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
public actual open class LockFreeLinkedListHead : LockFreeLinkedListNode() {
    /**
     * Iterates over all elements in this list of a specified type.
     */
    public actual inline fun forEach(startAfter: LockFreeLinkedListNode?, block: (Node) -> Unit) {
        var cur: Node = startAfter ?: this
        while (cur.isRemoved) cur = cur.prevNode // rollback to prev non-removed (or list head)
        cur = cur.nextNode
        while (cur !== this) {
            if (!cur.isRemoved) {
                block(cur)
            }
            cur = cur.nextNode
        }
    }

    // just a defensive programming -- makes sure that list head sentinel is never removed
    public final override fun remove(): Nothing = error("head cannot be removed")

    // optimization: because head is never removed, we don't have to read _next.value to check these:
    override val isRemoved: Boolean get() = false

    /**
     * Forbids adding new items to this list.
     */
    public actual fun close(forbiddenElementsBit: Int) {
        addLast(ListClosed(forbiddenElementsBit), forbiddenElementsBit)
    }
}

private class ListClosed(val forbiddenElementsBitmask: Int): LockFreeLinkedListNode()
