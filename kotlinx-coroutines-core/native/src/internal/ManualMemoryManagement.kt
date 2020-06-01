/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

@Suppress("NOTHING_TO_INLINE")
internal actual inline fun disposeLockFreeLinkedList(list: () -> LockFreeLinkedListNode?) {
    // only needed on Kotlin/Native
    val head = list() ?: return
    var cur = head
    do {
        val next = cur.nextNode // returns cur when already unlinked last node
        val last = next === head || next === cur
        cur.unlinkRefs(last)
        cur = next
    } while (!last)
}

@Suppress("NOTHING_TO_INLINE")
internal actual inline fun storeCyclicRef(block: () -> Unit) {} // nop on native
