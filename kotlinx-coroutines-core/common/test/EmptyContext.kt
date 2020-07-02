/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.intrinsics.*
import kotlin.coroutines.*

suspend fun <T> withEmptyContext(block: suspend () -> T): T {
    val baseline = Result.failure<T>(IllegalStateException("Block was suspended"))
    var result: Result<T> = baseline
    block.startCoroutineUnintercepted(Continuation(EmptyCoroutineContext) { result = it })
    while (result == baseline) yield()
    return result.getOrThrow()
}
