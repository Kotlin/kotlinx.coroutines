/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

internal expect inline fun disposeLockFreeLinkedList(list: () -> LockFreeLinkedListNode?) // only needed on Kotlin/Native
internal expect inline fun storeCyclicRef(block: () -> Unit) // nop on native
