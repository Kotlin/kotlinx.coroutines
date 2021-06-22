/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("RedundantVisibilityModifier")

package kotlinx.coroutines.tasks

import com.google.android.gms.tasks.*
import kotlinx.coroutines.*
import kotlin.coroutines.*

/**
 * Converts this deferred to the instance of [Task].
 * If deferred is cancelled then resulting task will be cancelled as well.
 */
public fun <T> Deferred<T>.asTask(): Task<T> {
    val cancellation = CancellationTokenSource()
    val source = TaskCompletionSource<T>(cancellation.token)

    invokeOnCompletion callback@{
        if (it is CancellationException) {
            cancellation.cancel()
            return@callback
        }

        val t = getCompletionExceptionOrNull()
        if (t == null) {
            source.setResult(getCompleted())
        } else {
            source.setException(t as? Exception ?: RuntimeExecutionException(t))
        }
    }

    return source.task
}

/**
 * Converts this task to an instance of [Deferred].
 *
 * Prefer passing the corresponding [CancellationTokenSource] if the [Task] can be created with a [CancellationToken]
 * to support bi-directional cancellation.
 *
 * If task is cancelled then resulting deferred will be cancelled as well.
 */
public fun <T> Task<T>.asDeferred(): Deferred<T> = asDeferred(CancellationTokenSource())

/**
 * Converts this task to an instance of [Deferred] with a [CancellationTokenSource] to control cancellation.
 *
 * If the task is cancelled, then the resulting deferred will be cancelled.
 * When the deferred is completed, the [cancellationTokenSource] will be cancelled.
 *
 * Providing a [CancellationTokenSource] that is unrelated to the receiving [Task] is not supported, as this function
 * won't listen for the token being cancelled directly. Instead, prefer to just cancel the corresponding [Job].
 */
@ExperimentalCoroutinesApi
public fun <T> Task<T>.asDeferred(cancellationTokenSource: CancellationTokenSource): Deferred<T> {
    val deferred = CompletableDeferred<T>()

    if (isComplete) {
        val e = exception
        if (e == null) {
            if (isCanceled) {
                deferred.cancel()
            } else {
                @Suppress("UNCHECKED_CAST")
                deferred.complete(this.result as T)
            }
        } else {
            deferred.completeExceptionally(e)
        }
    } else {
        addOnCompleteListener {
            val e = it.exception
            if (e == null) {
                @Suppress("UNCHECKED_CAST")
                if (it.isCanceled) deferred.cancel() else deferred.complete(it.result as T)
            } else {
                deferred.completeExceptionally(e)
            }
        }
    }

    deferred.invokeOnCompletion {
        cancellationTokenSource.cancel()
    }

    return object : Deferred<T> by deferred {}
}

/**
 * Awaits for completion of the task without blocking a thread.
 *
 * Prefer passing the corresponding [CancellationTokenSource] if the [Task] can be created with a [CancellationToken]
 * to support bi-directional cancellation.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * stops waiting for the completion stage and immediately resumes with [CancellationException].
 */
public suspend fun <T> Task<T>.await(): T = await(CancellationTokenSource())

/**
 * Awaits for completion of the task that is linked to the given [CancellationTokenSource] to control cancellation.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * cancels the [cancellationTokenSource] and throws a [CancellationException].
 * If the task is cancelled, then this function will throw a [CancellationException].
 *
 * Providing a [CancellationTokenSource] that is unrelated to the receiving [Task] is not supported, as this function
 * won't listen for the token being cancelled directly. Instead, prefer to just cancel the corresponding [Job].
 */
@ExperimentalCoroutinesApi
public suspend fun <T> Task<T>.await(cancellationTokenSource: CancellationTokenSource): T {
    // fast path
    if (isComplete) {
        val e = exception
        return if (e == null) {
            if (isCanceled) {
                throw CancellationException("Task $this was cancelled normally.")
            } else {
                @Suppress("UNCHECKED_CAST")
                result as T
            }
        } else {
            throw e
        }
    }

    return suspendCancellableCoroutine { cont ->
        addOnCompleteListener {
            val e = it.exception
            if (e == null) {
                @Suppress("UNCHECKED_CAST")
                if (it.isCanceled) cont.cancel() else cont.resume(it.result as T)
            } else {
                cont.resumeWithException(e)
            }
        }

        cont.invokeOnCancellation {
            cancellationTokenSource.cancel()
        }
    }
}
