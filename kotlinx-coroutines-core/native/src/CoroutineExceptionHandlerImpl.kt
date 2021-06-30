/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.system.exitProcess
import kotlin.native.*
import kotlin.native.concurrent.*

internal actual fun handleCoroutineExceptionImpl(context: CoroutineContext, exception: Throwable) {
    // Use unhandled exception hook if it is set, otherwise print the stacktrace
    val hook = setUnhandledExceptionHook({ _: Throwable -> }.freeze())
    if (hook != null) hook(exception) else exception.printStackTrace()
    // Terminate the process
    exitProcess(-1)
}
