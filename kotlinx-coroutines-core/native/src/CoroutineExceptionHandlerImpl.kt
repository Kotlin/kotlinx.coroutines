/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.native.*

internal actual fun initializeDefaultExceptionHandlers() {
    // Do nothing
}

@OptIn(ExperimentalStdlibApi::class)
internal actual fun handleCoroutineExceptionImpl(context: CoroutineContext, exception: Throwable) {
    // log exception
    processUnhandledException(exception)
}
