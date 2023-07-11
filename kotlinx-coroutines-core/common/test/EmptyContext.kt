/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.intrinsics.*
import kotlin.coroutines.*

suspend fun <T> withEmptyContext(block: suspend () -> T): T = suspendCoroutine { cont ->
    block.startCoroutineUnintercepted(Continuation(EmptyCoroutineContext) { cont.resumeWith(it) })
}
