/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.io.jvm.javaio

import kotlinx.io.pool.*

internal val ByteArrayPool = object : DefaultPool<ByteArray>(128) {
    override fun produceInstance() = ByteArray(4096)
}