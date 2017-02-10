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

import java.util.concurrent.atomic.AtomicIntegerFieldUpdater
import java.util.concurrent.atomic.AtomicReferenceFieldUpdater

private typealias Node = LockFreeLinkedListNode

@PublishedApi
internal const val UNDECIDED = 0

@PublishedApi
internal const val SUCCESS = 1

@PublishedApi
internal const val FAILURE = 2

/**
 * Doubly-linked concurrent list node with remove support.
 * Based on paper
 * ["Lock-Free and Practical Doubly Linked List-Based Deques Using Single-Word Compare-and-Swap"](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.140.4693&rep=rep1&type=pdf)
 * by Sundell and Tsigas.
 * The instance of this class serves both as list head/tail sentinel and as the list item.
 * Sentinel node should be never removed.
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
@Suppress("LeakingThis")
public open class LockFreeLinkedListNode {
    @Volatile
    private var _next: Any = this // DoubleLinkedNode | Removed | CondAdd
    @Volatile
    private var prev: Any = this // DoubleLinkedNode | Removed
    @Volatile
    private var removedRef: Removed? = null // lazily cached removed ref to this

    private companion object {
        @JvmStatic
        val NEXT: AtomicReferenceFieldUpdater<Node, Any> =
                AtomicReferenceFieldUpdater.newUpdater(Node::class.java, Any::class.java, "_next")
        @JvmStatic
        val PREV: AtomicReferenceFieldUpdater<Node, Any> =
                AtomicReferenceFieldUpdater.newUpdater(Node::class.java, Any::class.java, "prev")
        @JvmStatic
        val REMOVED_REF: AtomicReferenceFieldUpdater<Node, Removed?> =
            AtomicReferenceFieldUpdater.newUpdater(Node::class.java, Removed::class.java, "removedRef")
    }

    private class Removed(val ref: Node) {
        override fun toString(): String = "Removed[$ref]"
    }

    private fun removed(): Removed =
        removedRef ?: Removed(this).also { REMOVED_REF.lazySet(this, it) }

    @PublishedApi
    internal abstract class CondAdd(val newNode: Node) {
        lateinit var oldNext: Node
        @Volatile
        private var consensus: Int = UNDECIDED // status of operation

        abstract fun isCondition(): Boolean

        private companion object {
            @JvmStatic
            val CONSENSUS: AtomicIntegerFieldUpdater<CondAdd> =
                    AtomicIntegerFieldUpdater.newUpdater(CondAdd::class.java, "consensus")
        }

        // returns either SUCCESS or FAILURE
        fun completeAdd(node: Node): Int {
            // make decision on status
            var consensus: Int
            while (true) {
                consensus = this.consensus
                if (consensus != UNDECIDED) break
                val proposal = if (isCondition()) SUCCESS else FAILURE
                if (CONSENSUS.compareAndSet(this, UNDECIDED, proposal)) {
                    consensus = proposal
                    break
                }
            }
            val success = consensus == SUCCESS
            if (NEXT.compareAndSet(node, this, if (success) newNode else oldNext)) {
                // only the thread the makes this update actually finishes add operation
                if (success) newNode.finishAdd(oldNext)
            }
            return consensus
        }
    }

    @PublishedApi
    internal inline fun makeCondAdd(node: Node, crossinline condition: () -> Boolean): CondAdd = object : CondAdd(node) {
        override fun isCondition(): Boolean = condition()
    }

    public val isRemoved: Boolean get() = _next is Removed

    private val isFresh: Boolean get() = _next === this && prev === this

    @PublishedApi
    internal val next: Any get() {
        while (true) { // helper loop on _next
            val next = this._next
            if (next !is CondAdd) return next
            next.completeAdd(this)
        }
    }

    public fun next(): Node = next.unwrap()

    public fun prev(): Node {
        while (true) {
            prevHelper()?.let { return it.unwrap() }
        }
    }

    // ------ addFirstXXX ------

    /**
     * Adds first item to this list.
     */
    public fun addFirst(node: Node) {
        while (true) { // lock-free loop on next
            val next = this.next as Node // this sentinel node is never removed
            if (addNext(node, next)) return
        }
    }

    /**
     * Adds first item to this list atomically if the [condition] is true.
     */
    public inline fun addFirstIf(node: Node, crossinline condition: () -> Boolean): Boolean {
        val condAdd = makeCondAdd(node, condition)
        while (true) { // lock-free loop on next
            val next = this.next as Node // this sentinel node is never removed
            when (tryCondAddNext(node, next, condAdd)) {
                SUCCESS -> return true
                FAILURE -> return false
            }
        }
    }

    public fun addFirstIfEmpty(node: Node): Boolean {
        PREV.lazySet(node, this)
        NEXT.lazySet(node, this)
        if (!NEXT.compareAndSet(this, this, node)) return false // this is not an empty list!
        // added successfully (linearized add) -- fixup the list
        node.finishAdd(this)
        return true
    }

    // ------ addLastXXX ------

    /**
     * Adds last item to this list.
     */
    public fun addLast(node: Node) {
        while (true) { // lock-free loop on prev.next
            val prev = prevHelper() ?: continue
            if (prev.addNext(node, this)) return
        }
    }

    /**
     * Adds last item to this list atomically if the [condition] is true.
     */
    public inline fun addLastIf(node: Node, crossinline condition: () -> Boolean): Boolean {
        val condAdd = makeCondAdd(node, condition)
        while (true) { // lock-free loop on prev.next
            val prev = prevHelper() ?: continue
            when (prev.tryCondAddNext(node, this, condAdd)) {
                SUCCESS -> return true
                FAILURE -> return false
            }
        }
    }

    public inline fun addLastIfPrev(node: Node, predicate: (Node) -> Boolean): Boolean {
        while (true) { // lock-free loop on prev.next
            val prev = prevHelper() ?: continue
            if (!predicate(prev)) return false
            if (prev.addNext(node, this)) return true
        }
    }

    public inline fun addLastIfPrevAndIf(
            node: Node,
            predicate: (Node) -> Boolean, // prev node predicate
            crossinline condition: () -> Boolean // atomically checked condition
    ): Boolean {
        val condAdd = makeCondAdd(node, condition)
        while (true) { // lock-free loop on prev.next
            val prev = prevHelper() ?: continue
            if (!predicate(prev)) return false
            when (prev.tryCondAddNext(node, this, condAdd)) {
                SUCCESS -> return true
                FAILURE -> return false
            }
        }
    }

    @PublishedApi
    internal fun prevHelper(): Node? {
        val prev = this.prev as Node // this sentinel node is never removed
        if (prev.next === this) return prev
        helpInsert(prev)
        return null
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
    internal fun tryCondAddNext(node: Node, next: Node, condAdd: CondAdd): Int {
        PREV.lazySet(node, this)
        NEXT.lazySet(node, next)
        condAdd.oldNext = next
        if (!NEXT.compareAndSet(this, next, condAdd)) return UNDECIDED
        // added operation successfully (linearized) -- complete it & fixup the list
        return condAdd.completeAdd(this)
    }

    // ------ removeXXX ------

    /**
     * Removes this node from the list. Returns `true` when removed successfully.
     */
    public open fun remove(): Boolean {
        while (true) { // lock-free loop on next
            val next = this.next
            if (next is Removed) return false // was already removed -- don't try to help (original thread will take care)
            if (NEXT.compareAndSet(this, next, (next as Node).removed())) {
                // was removed successfully (linearized remove) -- fixup the list
                helpDelete()
                next.helpInsert(prev.unwrap())
                return true
            }
        }
    }

    public fun removeFirstOrNull(): Node? {
        while (true) { // try to linearize
            val first = next()
            if (first == this) return null
            if (first.remove()) return first
        }
    }

    public inline fun <reified T> removeFirstIfIsInstanceOf(): T? {
        while (true) { // try to linearize
            val first = next()
            if (first == this) return null
            if (first !is T) return null
            if (first.remove()) return first
        }
    }

    // just peek at item when predicate is true
    public inline fun <reified T> removeFirstIfIsInstanceOfOrPeekIf(predicate: (T) -> Boolean): T? {
        while (true) { // try to linearize
            val first = next()
            if (first == this) return null
            if (first !is T) return null
            if (predicate(first)) return first // just peek when predicate is true
            if (first.remove()) return first
        }
    }

    // ------ other helpers ------

    private fun finishAdd(next: Node) {
        while (true) {
            val nextPrev = next.prev
            if (nextPrev is Removed || this.next !== next) return // next was removed, remover fixes up links
            if (PREV.compareAndSet(next, nextPrev, this)) {
                if (this.next is Removed) {
                    // already removed
                    next.helpInsert(nextPrev as Node)
                }
                return
            }
        }
    }

    private fun markPrev(): Node {
        while (true) { // lock-free loop on prev
            val prev = this.prev
            if (prev is Removed) return prev.ref
            if (PREV.compareAndSet(this, prev, (prev as Node).removed())) return prev
        }
    }

    // fixes next links to the left of this node
    private fun helpDelete() {
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
                    prev = prev.prev.unwrap()
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
    private fun helpInsert(_prev: Node) {
        var prev: Node = _prev
        var last: Node? = null // will be set so that last.next === prev
        while (true) {
            // move the the left until first non-removed node
            val prevNext = prev.next
            if (prevNext is Removed) {
                if (last !== null) {
                    prev.markPrev()
                    NEXT.compareAndSet(last, prev, prevNext.ref)
                    prev = last
                    last = null
                } else {
                    prev = prev.prev.unwrap()
                }
                continue
            }
            val oldPrev = this.prev
            if (oldPrev is Removed) return // this node was removed, too -- its remover will take care
            if (prevNext !== this) {
                // need to fixup next
                last = prev
                prev = prevNext as Node
                continue
            }
            if (oldPrev === prev) return // it is already linked as needed
            if (PREV.compareAndSet(this, oldPrev, prev)) {
                if (prev.prev !is Removed) return // finish only if prev was not concurrently removed
            }
        }
    }

    private fun Any.unwrap(): Node = if (this is Removed) ref else this as Node

    internal fun validateNode(prev: Node, next: Node) {
        check(prev === this.prev)
        check(next === this.next)
    }
}

/**
 * Head (sentinel) item of the linked list that is never removed.
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
public open class LockFreeLinkedListHead : LockFreeLinkedListNode() {
    public val isEmpty: Boolean get() = next() == this

    /**
     * Iterates over all elements in this list of a specified type.
     */
    public inline fun <reified T : Node> forEach(block: (T) -> Unit) {
        var cur: Node = next()
        while (cur != this) {
            if (cur is T) block(cur)
            cur = cur.next()
        }
    }

    // just a defensive programming -- makes sure that list head sentinel is never removed
    public final override fun remove() = throw UnsupportedOperationException()

    internal fun validate() {
        var prev: Node = this
        var cur: Node = next()
        while (cur != this) {
            val next = cur.next()
            cur.validateNode(prev, next)
            prev = cur
            cur = next
        }
        validateNode(prev, next())
    }
}
