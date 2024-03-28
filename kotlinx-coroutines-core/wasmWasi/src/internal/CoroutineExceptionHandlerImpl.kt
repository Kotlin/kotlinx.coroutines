/*
 * Copyright 2016-2024 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

internal actual fun propagateExceptionFinalResort(exception: Throwable) {
    println(exception.toString())
}