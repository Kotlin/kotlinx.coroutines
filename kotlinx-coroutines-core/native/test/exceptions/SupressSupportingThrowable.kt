/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.exceptions

import kotlinx.coroutines.*

internal actual typealias SuppressSupportingThrowable = SuppressSupportingThrowableImpl

actual val Throwable.suppressed: Array<Throwable>
    get() = (this as? SuppressSupportingThrowableImpl)?.suppressed ?: emptyArray()

@Suppress("EXTENSION_SHADOWED_BY_MEMBER")
actual fun Throwable.printStackTrace() = printStackTrace()

