/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")

package kotlinx.coroutines.internal

import kotlin.internal.*

@InlineOnly
@Suppress("NOTHING_TO_INLINE") // Should be NOP
internal actual inline fun disposeLockFreeLinkedList(list: () -> LockFreeLinkedListNode?) {} // only needed on Kotlin/Native

@InlineOnly
@Suppress("NOTHING_TO_INLINE")
internal actual inline fun storeCyclicRef(block: () -> Unit) = block()
