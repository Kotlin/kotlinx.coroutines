/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.functions.*
import io.reactivex.plugins.*
import kotlinx.coroutines.*
import kotlin.coroutines.*

internal class RxCancellable(private val job: Job) : Cancellable {
    override fun cancel() {
        job.cancel()
    }
}

internal fun handleUndeliverableException(cause: Throwable, context: CoroutineContext) {
    if (cause is CancellationException) return // Async CE should be completely ignored
    try {
        RxJavaPlugins.onError(cause)
    } catch (e: Throwable) {
        handleCoroutineException(context, cause)
    }
}