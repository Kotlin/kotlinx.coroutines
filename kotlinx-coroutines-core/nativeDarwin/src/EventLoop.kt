/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.cinterop.*

internal actual inline fun platformAutoreleasePool(crossinline block: () -> Unit): Unit = autoreleasepool { block() }
