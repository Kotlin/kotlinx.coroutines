/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.exceptions

import kotlinx.coroutines.*
import java.io.*
import java.util.*
import kotlin.coroutines.*
import kotlin.test.*

/**
 * Proxy for [Throwable.getSuppressed] for tests, which are compiled for both JDK 1.6 and JDK 1.8,
 * but run only under JDK 1.8
 */
@Suppress("ConflictingExtensionProperty")
actual val Throwable.suppressed: Array<Throwable> get() {
    val method = this::class.java.getMethod("getSuppressed") ?: error("This test can only be run using JDK 1.7")
    @Suppress("UNCHECKED_CAST")
    return method.invoke(this) as Array<Throwable>
}

