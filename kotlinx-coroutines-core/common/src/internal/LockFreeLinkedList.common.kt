/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("NO_EXPLICIT_VISIBILITY_IN_API_MODE")

package kotlinx.coroutines.internal

import kotlin.jvm.*
import kotlin.native.concurrent.*

/** @suppress **This is unstable API and it is subject to change.** */
public expect open class LockFreeLinkedListNode() {
    public val isRemoved: Boolean
    public val nextNode: LockFreeLinkedListNode
    public val prevNode: LockFreeLinkedListNode
    public fun addLast(node: LockFreeLinkedListNode)
    public fun addOneIfEmpty(node: LockFreeLinkedListNode): Boolean
    public inline fun addLastIfPrev(
        node: LockFreeLinkedListNode,
        predicate: (LockFreeLinkedListNode) -> Boolean
    ): Boolean

    public inline fun addLastIfPrevAndIf(
        node: LockFreeLinkedListNode,
        predicate: (LockFreeLinkedListNode) -> Boolean, // prev node predicate
        crossinline condition: () -> Boolean // atomically checked condition
    ): Boolean

    public open fun remove(): Boolean

    /**
     * Helps fully finish [remove] operation, must be invoked after [remove] if needed.
     * Ensures that traversing the list via prev pointers sees this node as removed.
     * No-op on JS
     */
    public fun helpRemove()
    public fun removeFirstOrNull(): LockFreeLinkedListNode?
    public inline fun <reified T> removeFirstIfIsInstanceOfOrPeekIf(predicate: (T) -> Boolean): T?
}

/** @suppress **This is unstable API and it is subject to change.** */
public expect open class LockFreeLinkedListHead() : LockFreeLinkedListNode {
    public val isEmpty: Boolean
    public inline fun <reified T : LockFreeLinkedListNode> forEach(block: (T) -> Unit)
    public final override fun remove(): Nothing
}

/** @suppress **This is unstable API and it is subject to change.** */
public expect open class AddLastDesc<T : LockFreeLinkedListNode>(
    queue: LockFreeLinkedListNode,
    node: T
) : AbstractAtomicDesc {
    val queue: LockFreeLinkedListNode
    val node: T
    override fun finishPrepare(prepareOp: PrepareOp)
    override fun finishOnSuccess(affected: LockFreeLinkedListNode, next: LockFreeLinkedListNode)
}

/** @suppress **This is unstable API and it is subject to change.** */
public expect open class RemoveFirstDesc<T>(queue: LockFreeLinkedListNode): AbstractAtomicDesc {
    val queue: LockFreeLinkedListNode
    public val result: T
    override fun finishPrepare(prepareOp: PrepareOp)
    final override fun finishOnSuccess(affected: LockFreeLinkedListNode, next: LockFreeLinkedListNode)
}

/** @suppress **This is unstable API and it is subject to change.** */
public expect abstract class AbstractAtomicDesc : AtomicDesc {
    final override fun prepare(op: AtomicOp<*>): Any?
    final override fun complete(op: AtomicOp<*>, failure: Any?)
    protected open fun failure(affected: LockFreeLinkedListNode): Any?
    protected open fun retry(affected: LockFreeLinkedListNode, next: Any): Boolean
    public abstract fun finishPrepare(prepareOp: PrepareOp) // non-null on failure
    public open fun onPrepare(prepareOp: PrepareOp): Any? // non-null on failure
    public open fun onRemoved(affected: LockFreeLinkedListNode) // non-null on failure
    protected abstract fun finishOnSuccess(affected: LockFreeLinkedListNode, next: LockFreeLinkedListNode)
}

/** @suppress **This is unstable API and it is subject to change.** */
public expect class PrepareOp: OpDescriptor {
    val affected: LockFreeLinkedListNode
    override val atomicOp: AtomicOp<*>
    val desc: AbstractAtomicDesc
    fun finishPrepare()
}

@JvmField
@SharedImmutable
internal val REMOVE_PREPARED: Any = Symbol("REMOVE_PREPARED")
