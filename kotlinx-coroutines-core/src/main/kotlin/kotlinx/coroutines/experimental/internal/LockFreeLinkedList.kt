/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental.internal

import java.util.concurrent.atomic.AtomicReferenceFieldUpdater

private typealias Node = LockFreeLinkedListNode

@PublishedApi
internal const val UNDECIDED = 0

@PublishedApi
internal const val SUCCESS = 1

@PublishedApi
internal const val FAILURE = 2

@PublishedApi
internal val CONDITION_FALSE: Any = Symbol("CONDITION_FALSE")

@PublishedApi
internal val ALREADY_REMOVED: Any = Symbol("ALREADY_REMOVED")

@PublishedApi
internal val LIST_EMPTY: Any = Symbol("LIST_EMPTY")

private val REMOVE_PREPARED: Any = Symbol("REMOVE_PREPARED")

/**
 * @suppress **This is unstable API and it is subject to change.**
 */
public typealias RemoveFirstDesc<T> = LockFreeLinkedListNode.RemoveFirstDesc<T>

/**
 * @suppress **This is unstable API and it is subject to change.**
 */
public typealias AddLastDesc<T> = LockFreeLinkedListNode.AddLastDesc<T>

/**
 * Doubly-linked concurrent list node with remove support.
 * Based on paper
 * ["Lock-Free and Practical Doubly Linked List-Based Deques Using Single-Word Compare-and-Swap"](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.140.4693&rep=rep1&type=pdf)
 * by Sundell and Tsigas.
 *
 * Important notes:
 * * The instance of this class serves both as list head/tail sentinel and as the list item.
 *   Sentinel node should be never removed.
 * * There are no operations to add items to left side of the list, only to the end (right side), because we cannot
 *   efficiently linearize them with atomic multi-step head-removal operations. In short,
 *   support for [describeRemoveFirst] operation precludes ability to add items at the beginning.
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
@Suppress("LeakingThis")
public open class LockFreeLinkedListNode {
    @Volatile
    private var _next: Any = this // Node | Removed | OpDescriptor
    @Volatile
    private var _prev: Any = this // Node | Removed
    @Volatile
    private var _removedRef: Removed? = null // lazily cached removed ref to this

    private companion object {
        @JvmField
        val NEXT: AtomicReferenceFieldUpdater<Node, Any> =
                AtomicReferenceFieldUpdater.newUpdater(Node::class.java, Any::class.java, "_next")
        @JvmField
        val PREV: AtomicReferenceFieldUpdater<Node, Any> =
                AtomicReferenceFieldUpdater.newUpdater(Node::class.java, Any::class.java, "_prev")
        @JvmField
        val REMOVED_REF: AtomicReferenceFieldUpdater<Node, Removed?> =
            AtomicReferenceFieldUpdater.newUpdater(Node::class.java, Removed::class.java, "_removedRef")
    }

    private fun removed(): Removed =
        _removedRef ?: Removed(this).also { REMOVED_REF.lazySet(this, it) }

    @PublishedApi
    internal abstract class CondAddOp(
        @JvmField val newNode: Node
    ) : AtomicOp() {
        @JvmField var oldNext: Node? = null

        override fun complete(affected: Any?, failure: Any?) {
            affected as Node // type assertion
            val success = failure == null
            val update = if (success) newNode else oldNext
            if (NEXT.compareAndSet(affected, this, update)) {
                // only the thread the makes this update actually finishes add operation
                if (success) newNode.finishAdd(oldNext!!)
            }
        }
    }

    @PublishedApi
    internal inline fun makeCondAddOp(node: Node, crossinline condition: () -> Boolean): CondAddOp =
        object : CondAddOp(node) {
            override fun prepare(): Any? = if (condition()) null else CONDITION_FALSE
        }

    public val isRemoved: Boolean get() = next is Removed

    // LINEARIZABLE. Returns Node | Removed
    public val next: Any get() {
        while (true) { // operation helper loop on _next
            val next = this._next
            if (next !is OpDescriptor) return next
            next.perform(this)
        }
    }

    // LINEARIZABLE. Returns Node | Removed
    public val prev: Any get() {
        while (true) { // insert helper loop on _prev
            val prev = this._prev
            if (prev is Removed) return prev
            prev as Node // otherwise, it can be only node otherwise
            if (prev.next === this) return prev
            helpInsert(prev, null)
        }
    }

    // ------ addOneIfEmpty ------

    public fun addOneIfEmpty(node: Node): Boolean {
        PREV.lazySet(node, this)
        NEXT.lazySet(node, this)
        while (true) {
            val next = next
            if (next !== this) return false // this is not an empty list!
            if (NEXT.compareAndSet(this, this, node)) {
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
    public fun addLast(node: Node) {
        while (true) { // lock-free loop on prev.next
            val prev = prev as Node // sentinel node is never removed, so prev is always defined
            if (prev.addNext(node, this)) return
        }
    }

    public fun <T : Node> describeAddLast(node: T): AddLastDesc<T> = AddLastDesc(this, node)

    /**
     * Adds last item to this list atomically if the [condition] is true.
     */
    public inline fun addLastIf(node: Node, crossinline condition: () -> Boolean): Boolean {
        val condAdd = makeCondAddOp(node, condition)
        while (true) { // lock-free loop on prev.next
            val prev = prev as Node // sentinel node is never removed, so prev is always defined
            when (prev.tryCondAddNext(node, this, condAdd)) {
                SUCCESS -> return true
                FAILURE -> return false
            }
        }
    }

    public inline fun addLastIfPrev(node: Node, predicate: (Node) -> Boolean): Boolean {
        while (true) { // lock-free loop on prev.next
            val prev = prev as Node // sentinel node is never removed, so prev is always defined
            if (!predicate(prev)) return false
            if (prev.addNext(node, this)) return true
        }
    }

    public inline fun addLastIfPrevAndIf(
            node: Node,
            predicate: (Node) -> Boolean, // prev node predicate
            crossinline condition: () -> Boolean // atomically checked condition
    ): Boolean {
        val condAdd = makeCondAddOp(node, condition)
        while (true) { // lock-free loop on prev.next
            val prev = prev as Node // sentinel node is never removed, so prev is always defined
            if (!predicate(prev)) return false
            when (prev.tryCondAddNext(node, this, condAdd)) {
                SUCCESS -> return true
                FAILURE -> return false
            }
        }
    }

    // ------ addXXX util ------

    @PublishedApi
    internal fun addNext(node: Node, next: Node): Boolean {
        PREV.lazySet(node, this)
        NEXT.lazySet(node, next)
        if (!NEXT.compareAndSet(this, next, node)) return false
        // added successfully (linearized add) -- fixup the list
        node.finishAdd(next)
        return true
    }

    // returns UNDECIDED, SUCCESS or FAILURE
    @PublishedApi
    internal fun tryCondAddNext(node: Node, next: Node, condAdd: CondAddOp): Int {
        PREV.lazySet(node, this)
        NEXT.lazySet(node, next)
        condAdd.oldNext = next
        if (!NEXT.compareAndSet(this, next, condAdd)) return UNDECIDED
        // added operation successfully (linearized) -- complete it & fixup the list
        return if (condAdd.perform(this) == null) SUCCESS else FAILURE
    }

    // ------ removeXXX ------

    /**
     * Removes this node from the list. Returns `true` when removed successfully.
     */
    public open fun remove(): Boolean {
        while (true) { // lock-free loop on next
            val next = this.next
            if (next is Removed) return false // was already removed -- don't try to help (original thread will take care)
            check(next !== this) // sanity check -- can be true for sentinel nodes only, but they are never removed
            val removed = (next as Node).removed()
            if (NEXT.compareAndSet(this, next, removed)) {
                // was removed successfully (linearized remove) -- fixup the list
                finishRemove(next)
                return true
            }
        }
    }

    public open fun describeRemove() : AtomicDesc? {
        if (isRemoved) return null // fast path if was already removed
        return object : AbstractAtomicDesc() {
            override val affectedNode: Node? get() = this@LockFreeLinkedListNode
            override var originalNext: Node? = null
            override fun failure(affected: Node, next: Any): Any? =
                if (next is Removed) ALREADY_REMOVED else null
            override fun onPrepare(affected: Node, next: Node): Any? {
                originalNext = next
                return null // always success
            }
            override fun updatedNext(affected: Node, next: Node) = next.removed()
            override fun finishOnSuccess(affected: Node, next: Node) = finishRemove(next)
        }
    }

    public fun removeFirstOrNull(): Node? {
        while (true) { // try to linearize
            val first = next as Node
            if (first === this) return null
            if (first.remove()) return first
            first.helpDelete() // must help delete, or loose lock-freedom
        }
    }

    public fun describeRemoveFirst(): RemoveFirstDesc<Node> = RemoveFirstDesc(this)

    public inline fun <reified T> removeFirstIfIsInstanceOf(): T? {
        while (true) { // try to linearize
            val first = next as Node
            if (first === this) return null
            if (first !is T) return null
            if (first.remove()) return first
            first.helpDelete() // must help delete, or loose lock-freedom
        }
    }

    // just peek at item when predicate is true
    public inline fun <reified T> removeFirstIfIsInstanceOfOrPeekIf(predicate: (T) -> Boolean): T? {
        while (true) { // try to linearize
            val first = next as Node
            if (first === this) return null
            if (first !is T) return null
            if (predicate(first)) return first // just peek when predicate is true
            if (first.remove()) return first
            first.helpDelete() // must help delete, or loose lock-freedom
        }
    }

    // ------ multi-word atomic operations helpers ------

    public open class AddLastDesc<out T : Node>(
        @JvmField val queue: Node,
        @JvmField val node: T
    ) : AbstractAtomicDesc() {
        init {
            // require freshly allocated node here
            check(node._next === node && node._prev === node)
        }

        final override fun takeAffectedNode(op: OpDescriptor): Node {
            while (true) {
                val prev = queue._prev as Node // this sentinel node is never removed
                val next = prev._next
                if (next === queue) return prev // all is good -> linked properly
                if (next === op) return prev // all is good -> our operation descriptor is already there
                if (next is OpDescriptor) { // some other operation descriptor -> help & retry
                    next.perform(prev)
                    continue
                }
                // linked improperly -- help insert
                queue.helpInsert(prev, op)
            }
        }

        final override var affectedNode: Node? = null
        final override val originalNext: Node? get() = queue

        override fun retry(affected: Node, next: Any): Boolean = next !== queue

        override fun onPrepare(affected: Node, next: Node): Any? {
            affectedNode = affected
            return null // always success
        }

        override fun updatedNext(affected: Node, next: Node): Any {
            // it is invoked only on successfully completion of operation, but this invocation can be stale,
            // so we must use CAS to set both prev & next pointers
            PREV.compareAndSet(node, node, affected)
            NEXT.compareAndSet(node, node, queue)
            return node
        }

        override fun finishOnSuccess(affected: Node, next: Node) {
            node.finishAdd(queue)
        }
    }

    public open class RemoveFirstDesc<T>(
        @JvmField val queue: Node
    ) : AbstractAtomicDesc() {
        @Suppress("UNCHECKED_CAST")
        public val result: T get() = affectedNode!! as T

        final override fun takeAffectedNode(op: OpDescriptor): Node = queue.next as Node
        final override var affectedNode: Node? = null
        final override var originalNext: Node? = null

        // check node predicates here, must signal failure if affect is not of type T
        protected override fun failure(affected: Node, next: Any): Any? =
                if (affected === queue) LIST_EMPTY else null

        // validate the resulting node (return false if it should be deleted)
        protected open fun validatePrepared(node: T): Boolean = true // false means remove node & retry

        final override fun retry(affected: Node, next: Any): Boolean {
            if (next !is Removed) return false
            affected.helpDelete() // must help delete, or loose lock-freedom
            return true
        }

        @Suppress("UNCHECKED_CAST")
        final override fun onPrepare(affected: Node, next: Node): Any? {
            check(affected !is LockFreeLinkedListHead)
            if (!validatePrepared(affected as T)) return REMOVE_PREPARED
            affectedNode = affected
            originalNext = next
            return null // ok
        }

        final override fun updatedNext(affected: Node, next: Node): Any = next.removed()
        final override fun finishOnSuccess(affected: Node, next: Node) = affected.finishRemove(next)
    }

    public abstract class AbstractAtomicDesc : AtomicDesc() {
        protected abstract val affectedNode: Node?
        protected abstract val originalNext: Node?
        protected open fun takeAffectedNode(op: OpDescriptor): Node = affectedNode!!
        protected open fun failure(affected: Node, next: Any): Any? = null // next: Node | Removed
        protected open fun retry(affected: Node, next: Any): Boolean = false // next: Node | Removed
        protected abstract fun onPrepare(affected: Node, next: Node): Any? // non-null on failure
        protected abstract fun updatedNext(affected: Node, next: Node): Any
        protected abstract fun finishOnSuccess(affected: Node, next: Node)

        // This is Harris's RDCSS (Restricted Double-Compare Single Swap) operation
        // It inserts "op" descriptor of when "op" status is still undecided (rolls back otherwise)
        private class PrepareOp(
            @JvmField val next: Node,
            @JvmField val op: AtomicOp,
            @JvmField val desc: AbstractAtomicDesc
        ) : OpDescriptor() {
            override fun perform(affected: Any?): Any? {
                affected as Node // type assertion
                val decision = desc.onPrepare(affected, next)
                if (decision != null) {
                    if (decision === REMOVE_PREPARED) {
                        // remove element on failure
                        val removed = next.removed()
                        if (NEXT.compareAndSet(affected, this, removed)) {
                            affected.helpDelete()
                        }
                    } else {
                        // some other failure -- mark as decided
                        op.tryDecide(decision)
                        // undo preparations
                        NEXT.compareAndSet(affected, this, next)
                    }
                    return decision
                }
                check(desc.affectedNode === affected)
                check(desc.originalNext === next)
                val update: Any = if (op.isDecided) next else op // restore if decision was already reached
                NEXT.compareAndSet(affected, this, update)
                return null // ok
            }
        }

        final override fun prepare(op: AtomicOp): Any? {
            while (true) { // lock free loop on next
                val affected = takeAffectedNode(op)
                // read its original next pointer first
                val next = affected._next
                // then see if already reached consensus on overall operation
                if (op.isDecided) return null // already decided -- go to next desc
                if (next === op) return null // already in process of operation -- all is good
                if (next is OpDescriptor) {
                    // some other operation is in process -- help it
                    next.perform(affected)
                    continue // and retry
                }
                // next: Node | Removed
                val failure = failure(affected, next)
                if (failure != null) return failure // signal failure
                if (retry(affected, next)) continue // retry operation
                val prepareOp = PrepareOp(next as Node, op, this)
                if (NEXT.compareAndSet(affected, next, prepareOp)) {
                    // prepared -- complete preparations
                    val prepFail = prepareOp.perform(affected)
                    if (prepFail === REMOVE_PREPARED) continue // retry
                    return prepFail
                }
            }
        }

        final override fun complete(op: AtomicOp, failure: Any?) {
            val success = failure == null
            val affectedNode = affectedNode ?: run { check(!success); return }
            val originalNext = this.originalNext ?: run { check(!success); return }
            val update = if (success) updatedNext(affectedNode, originalNext) else originalNext
            if (NEXT.compareAndSet(affectedNode, op, update)) {
                if (success) finishOnSuccess(affectedNode, originalNext)
            }
        }
    }

    // ------ other helpers ------

    private fun finishAdd(next: Node) {
        while (true) {
            val nextPrev = next._prev
            if (nextPrev is Removed || this.next !== next) return // next was removed, remover fixes up links
            if (PREV.compareAndSet(next, nextPrev, this)) {
                if (this.next is Removed) {
                    // already removed
                    next.helpInsert(nextPrev as Node, null)
                }
                return
            }
        }
    }

    private fun finishRemove(next: Node) {
        helpDelete()
        next.helpInsert(_prev.unwrap(), null)
    }

    private fun markPrev(): Node {
        while (true) { // lock-free loop on prev
            val prev = this._prev
            if (prev is Removed) return prev.ref
            if (PREV.compareAndSet(this, prev, (prev as Node).removed())) return prev
        }
    }

    // fixes next links to the left of this node
    @PublishedApi
    internal fun helpDelete() {
        var last: Node? = null // will set to the node left of prev when found
        var prev: Node = markPrev()
        var next: Node = (this._next as Removed).ref
        while (true) {
            // move to the right until first non-removed node
            val nextNext = next.next
            if (nextNext is Removed) {
                next.markPrev()
                next = nextNext.ref
                continue
            }
            // move the the left until first non-removed node
            val prevNext = prev.next
            if (prevNext is Removed) {
                if (last != null) {
                    prev.markPrev()
                    NEXT.compareAndSet(last, prev, prevNext.ref)
                    prev = last
                    last = null
                } else {
                    prev = prev._prev.unwrap()
                }
                continue
            }
            if (prevNext !== this) {
                // skipped over some removed nodes to the left -- setup to fixup the next links
                last = prev
                prev = prevNext as Node
                if (prev === next) return // already done!!!
                continue
            }
            // Now prev & next are Ok
            if (NEXT.compareAndSet(prev, this, next)) return // success!
        }
    }

    // fixes prev links from this node
    private fun helpInsert(_prev: Node, op: OpDescriptor?) {
        var prev: Node = _prev
        var last: Node? = null // will be set so that last.next === prev
        while (true) {
            // move the the left until first non-removed node
            val prevNext = prev._next
            if (prevNext === op) return // part of the same op -- don't recurse
            if (prevNext is OpDescriptor) { // help & retry
                prevNext.perform(prev)
                continue
            }
            if (prevNext is Removed) {
                if (last !== null) {
                    prev.markPrev()
                    NEXT.compareAndSet(last, prev, prevNext.ref)
                    prev = last
                    last = null
                } else {
                    prev = prev._prev.unwrap()
                }
                continue
            }
            val oldPrev = this._prev
            if (oldPrev is Removed) return // this node was removed, too -- its remover will take care
            if (prevNext !== this) {
                // need to fixup next
                last = prev
                prev = prevNext as Node
                continue
            }
            if (oldPrev === prev) return // it is already linked as needed
            if (PREV.compareAndSet(this, oldPrev, prev)) {
                if (prev._prev !is Removed) return // finish only if prev was not concurrently removed
            }
        }
    }

    internal fun validateNode(prev: Node, next: Node) {
        check(prev === this._prev)
        check(next === this._next)
    }

    override fun toString(): String = "${this::class.java.simpleName}@${Integer.toHexString(System.identityHashCode(this))}"
}

private class Removed(@JvmField val ref: Node) {
    override fun toString(): String = "Removed[$ref]"
}

@PublishedApi
internal fun Any.unwrap(): Node = if (this is Removed) ref else this as Node

/**
 * Head (sentinel) item of the linked list that is never removed.
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
public open class LockFreeLinkedListHead : LockFreeLinkedListNode() {
    public val isEmpty: Boolean get() = next === this

    /**
     * Iterates over all elements in this list of a specified type.
     */
    public inline fun <reified T : Node> forEach(block: (T) -> Unit) {
        var cur: Node = next as Node
        while (cur != this) {
            if (cur is T) block(cur)
            cur = cur.next.unwrap()
        }
    }

    // just a defensive programming -- makes sure that list head sentinel is never removed
    public final override fun remove() = throw UnsupportedOperationException()
    public final override fun describeRemove(): AtomicDesc? = throw UnsupportedOperationException()

    internal fun validate() {
        var prev: Node = this
        var cur: Node = next as Node
        while (cur != this) {
            val next = cur.next.unwrap()
            cur.validateNode(prev, next)
            prev = cur
            cur = next
        }
        validateNode(prev, next as Node)
    }
}
