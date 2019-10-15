/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.native.concurrent.*

internal actual fun handleCoroutineExceptionImpl(context: CoroutineContext, exception: Throwable) {
    // log exception
//    println("Exception in \"${Worker.current}\"")
//    exception.printStackTrace()
// todo: printing exception does not make it easy to debug (no source location), so let it crash instead
    throw exception
}
