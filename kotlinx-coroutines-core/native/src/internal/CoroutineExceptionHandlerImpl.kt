/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlin.coroutines.*
import kotlin.native.*

internal actual val ANDROID_DETECTED = false

@OptIn(ExperimentalStdlibApi::class)
internal actual fun propagateExceptionToPlatform(context: CoroutineContext, exception: Throwable) {
    // log exception
    processUnhandledException(exception)
}
