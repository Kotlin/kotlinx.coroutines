/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.internal

import kotlin.jvm.*

internal object NullSurrogate {

    @Suppress("NULL_FOR_NONNULL_TYPE")
    @JvmStatic
    internal fun <T> unbox(value: Any?): T = if (value === NullSurrogate) null else value as T
}
