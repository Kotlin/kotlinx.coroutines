/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

@Suppress("NOTHING_TO_INLINE")
internal actual inline fun <T> clear(a: Array<T?>) = a.fill(null)