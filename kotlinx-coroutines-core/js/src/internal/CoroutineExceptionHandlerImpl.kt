/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import kotlin.coroutines.*

private val platformExceptionHandlers_ = mutableSetOf<CoroutineExceptionHandler>()

internal actual val platformExceptionHandlers: Collection<CoroutineExceptionHandler>
    get() = platformExceptionHandlers_

internal actual fun ensurePlatformExceptionHandlerLoaded(callback: CoroutineExceptionHandler) {
    platformExceptionHandlers_ += callback
}

internal actual fun propagateExceptionFinalResort(exception: Throwable) {
    // log exception
    console.error(exception)
}

internal actual class DiagnosticCoroutineContextException actual constructor(context: CoroutineContext) :
    RuntimeException(context.toString())

