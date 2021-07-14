/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

@Suppress("NOTHING_TO_INLINE")
internal actual inline fun disposeLockFreeLinkedList(list: () -> LockFreeLinkedListNode?) {} // only needed on Kotlin/Native

@Suppress("NOTHING_TO_INLINE")
internal actual inline fun storeCyclicRef(block: () -> Unit) = block()
