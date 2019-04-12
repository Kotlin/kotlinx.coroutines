/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.internal

import kotlin.jvm.*

internal object NullSurrogate {

    @JvmStatic
    @Suppress("UNCHECKED_CAST")
    internal fun <T> unbox(value: Any?): T = if (value === NullSurrogate) null as T else value as T
}
