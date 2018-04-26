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

/** @suppress **This is unstable API and it is subject to change.** */
public expect open class LockFreeLinkedListNode() {
    public val isRemoved: Boolean
    public val next: Any
    public val nextNode: LockFreeLinkedListNode
    public val prev: Any
    public val prevNode: LockFreeLinkedListNode
    public fun addLast(node: LockFreeLinkedListNode)
    public fun addOneIfEmpty(node: LockFreeLinkedListNode): Boolean
    public inline fun addLastIf(node: LockFreeLinkedListNode, crossinline condition: () -> Boolean): Boolean
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
    protected override fun onPrepare(affected: LockFreeLinkedListNode, next: LockFreeLinkedListNode): Any?
    override fun finishOnSuccess(affected: LockFreeLinkedListNode, next: LockFreeLinkedListNode)
}

public expect open class RemoveFirstDesc<T>(queue: LockFreeLinkedListNode): AbstractAtomicDesc {
    val queue: LockFreeLinkedListNode
    public val result: T
    protected open fun validatePrepared(node: T): Boolean
    protected final override fun onPrepare(affected: LockFreeLinkedListNode, next: LockFreeLinkedListNode): Any?
    final override fun finishOnSuccess(affected: LockFreeLinkedListNode, next: LockFreeLinkedListNode)
}

/** @suppress **This is unstable API and it is subject to change.** */
public expect abstract class AbstractAtomicDesc : AtomicDesc {
    final override fun prepare(op: AtomicOp<*>): Any?
    final override fun complete(op: AtomicOp<*>, failure: Any?)
    protected open fun failure(affected: LockFreeLinkedListNode, next: Any): Any?
    protected open fun retry(affected: LockFreeLinkedListNode, next: Any): Boolean
    protected abstract fun onPrepare(affected: LockFreeLinkedListNode, next: LockFreeLinkedListNode): Any? // non-null on failure
    protected abstract fun finishOnSuccess(affected: LockFreeLinkedListNode, next: LockFreeLinkedListNode)
}
