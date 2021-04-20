/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx3

import io.reactivex.rxjava3.functions.*
import io.reactivex.rxjava3.plugins.*
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
        cause.addSuppressed(e)
        handleCoroutineException(context, cause)
    }
}
