/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.exceptions

actual inline fun yieldThread() { Thread.yield() }

actual fun currentThreadName(): String = Thread.currentThread().name
