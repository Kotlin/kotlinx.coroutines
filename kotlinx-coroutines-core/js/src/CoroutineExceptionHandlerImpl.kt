/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*

internal actual fun handleCoroutineExceptionImpl(context: CoroutineContext, exception: Throwable) {
    // log exception
    console.error(exception)
}
