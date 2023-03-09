/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("NO_EXPLICIT_VISIBILITY_IN_API_MODE")

package kotlinx.coroutines.internal

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlin.jvm.*

private typealias Node = LockFreeLinkedListNode

@PublishedApi
internal const val UNDECIDED: Int = 0

@PublishedApi
internal const val SUCCESS: Int = 1

@PublishedApi
internal const val FAILURE: Int = 2

@PublishedApi
internal val CONDITION_FALSE: Any = Symbol("CONDITION_FALSE")

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
 * * There are no operations to add items to left side of the list, only to the end (right side), because we cannot
 *   efficiently linearize them with atomic multi-step head-removal operations. In short,
 *   support for [describeRemoveFirst] operation precludes ability to add items at the beginning.
 * * Previous pointers are not marked for removal. We don't support linearizable backwards traversal.
 * * Remove-helping logic is simplified and consolidated in [correctPrev] method.
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

    @PublishedApi
    internal abstract class CondAddOp(
        @JvmField val newNode: Node
    ) : AtomicOp<Node>() {
        @JvmField var oldNext: Node? = null

        override fun complete(affected: Node, failure: Any?) {
            val success = failure == null
            val update = if (success) newNode else oldNext
            if (update != null && affected._next.compareAndSet( this, update)) {
                // only the thread the makes this update actually finishes add operation
                if (success) newNode.finishAdd(oldNext!!)
            }
        }
    }

    @PublishedApi
    internal inline fun makeCondAddOp(node: Node, crossinline condition: () -> Boolean): CondAddOp =
        object : CondAddOp(node) {
            override fun prepare(affected: Node): Any? = if (condition()) null else CONDITION_FALSE
        }

    public actual open val isRemoved: Boolean get() = next is Removed

    // LINEARIZABLE. Returns Node | Removed
    public val next: Any get() {
        _next.loop { next ->
            if (next !is OpDescriptor) return next
            next.perform(this)
        }
    }

    // LINEARIZABLE. Returns next non-removed Node
    public actual val nextNode: Node get() = next.unwrap()

    // LINEARIZABLE WHEN THIS NODE IS NOT REMOVED:
    // Returns prev non-removed Node, makes sure prev is correct (prev.next === this)
    // NOTE: if this node is removed, then returns non-removed previous node without applying
    // prev.next correction, which does not provide linearizable backwards iteration, but can be used to
    // resume forward iteration when current node was removed.
    public actual val prevNode: Node
        get() = correctPrev(null) ?: findPrevNonRemoved(_prev.value)

    private tailrec fun findPrevNonRemoved(current: Node): Node {
        if (!current.isRemoved) return current
        return findPrevNonRemoved(current._prev.value)
    }

    // ------ addOneIfEmpty ------

    public actual fun addOneIfEmpty(node: Node): Boolean {
        node._prev.lazySet(this)
        node._next.lazySet(this)
        while (true) {
            val next = next
            if (next !== this) return false // this is not an empty list!
            if (_next.compareAndSet(this, node)) {
                // added successfully (linearized add) -- fixup the list
                node.finishAdd(this)
                return true
            }
        }
    }

    // ------ addLastXXX ------

    /**
     * Adds last item to this list.
     */
    public actual fun addLast(node: Node) {
        while (true) { // lock-free loop on prev.next
            if (prevNode.addNext(node, this)) return
        }
    }

    /**
     * Adds last item to this list atomically if the [condition] is true.
     */
    public actual inline fun addLastIf(node: Node, crossinline condition: () -> Boolean): Boolean {
        val condAdd = makeCondAddOp(node, condition)
        while (true) { // lock-free loop on prev.next
            val prev = prevNode // sentinel node is never removed, so prev is always defined
            when (prev.tryCondAddNext(node, this, condAdd)) {
                SUCCESS -> return true
                FAILURE -> return false
            }
        }
    }

    // ------ addXXX util ------

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

    // returns UNDECIDED, SUCCESS or FAILURE
    @PublishedApi
    internal fun tryCondAddNext(node: Node, next: Node, condAdd: CondAddOp): Int {
        node._prev.lazySet(this)
        node._next.lazySet(next)
        condAdd.oldNext = next
        if (!_next.compareAndSet(next, condAdd)) return UNDECIDED
        // added operation successfully (linearized) -- complete it & fixup the list
        return if (condAdd.perform(this) == null) SUCCESS else FAILURE
    }

    // ------ removeXXX ------

    /**
     * Removes this node from the list. Returns `true` when removed successfully, or `false` if the node was already
     * removed or if it was not added to any list in the first place.
     *
     * **Note**: Invocation of this operation does not guarantee that remove was actually complete if result was `false`.
     * In particular, invoking [nextNode].[prevNode] might still return this node even though it is "already removed".
     */
    public actual open fun remove(): Boolean =
        removeOrNext() == null

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
                next.correctPrev(null)
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
                if (isRemoved) next.correctPrev(null)
                return
            }
        }
    }

    protected open fun nextIfRemoved(): Node? = (next as? Removed)?.ref

    /**
     * Returns the corrected value of the previous node while also correcting the `prev` pointer
     * (so that `this.prev.next === this`) and helps complete node removals to the left ot this node.
     *
     * It returns `null` in two special cases:
     *
     * * When this node is removed. In this case there is no need to waste time on corrections, because
     *   remover of this node will ultimately call [correctPrev] on the next node and that will fix all
     *   the links from this node, too.
     */
    private tailrec fun correctPrev(op: OpDescriptor?): Node? {
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
                        return correctPrev(op)
                    }
                    return prev // return the correct prev
                }
                // slow path when we need to help remove operations
                this.isRemoved -> return null // nothing to do, this node was removed, bail out asap to save time
                prevNext === op -> return prev // part of the same op -- don't recurse, didn't correct prev
                prevNext is OpDescriptor -> { // help & retry
                    prevNext.perform(prev)
                    return correctPrev(op) // retry from scratch
                }
                prevNext is Removed -> {
                    if (last !== null) {
                        // newly added (prev) node is already removed, correct last.next around it
                        if (!last._next.compareAndSet(prev, prevNext.ref)) {
                            return correctPrev(op) // retry from scratch on failure to update next
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

@PublishedApi
internal fun Any.unwrap(): Node = (this as? Removed)?.ref ?: this as Node

/**
 * Head (sentinel) item of the linked list that is never removed.
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
public actual open class LockFreeLinkedListHead : LockFreeLinkedListNode() {
    public actual val isEmpty: Boolean get() = next === this

    /**
     * Iterates over all elements in this list of a specified type.
     */
    public actual inline fun <reified T : Node> forEach(block: (T) -> Unit) {
        var cur: Node = next as Node
        while (cur != this) {
            if (cur is T) block(cur)
            cur = cur.nextNode
        }
    }

    // just a defensive programming -- makes sure that list head sentinel is never removed
    public actual final override fun remove(): Nothing = error("head cannot be removed")

    // optimization: because head is never removed, we don't have to read _next.value to check these:
    override val isRemoved: Boolean get() = false
    override fun nextIfRemoved(): Node? = null

    internal fun validate() {
        var prev: Node = this
        var cur: Node = next as Node
        while (cur != this) {
            val next = cur.nextNode
            cur.validateNode(prev, next)
            prev = cur
            cur = next
        }
        validateNode(prev, next as Node)
    }
}
