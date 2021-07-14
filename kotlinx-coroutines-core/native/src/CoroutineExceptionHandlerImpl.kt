/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.system.exitProcess
import kotlin.native.*
import kotlin.native.concurrent.*
import kotlin.native.internal.OnUnhandledException

internal actual fun handleCoroutineExceptionImpl(context: CoroutineContext, exception: Throwable) {
    val throwable = Throwable(
        "The process was terminated due to the unhandled exception thrown in the coroutine $context: ${exception.message}",
        exception.cause)
    OnUnhandledException(throwable)
    // Terminate the process
    exitProcess(-1)
}
