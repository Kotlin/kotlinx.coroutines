/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("RedundantVisibilityModifier")

package kotlinx.coroutines.experimental.tasks

import com.google.android.gms.tasks.CancellationTokenSource
import com.google.android.gms.tasks.RuntimeExecutionException
import com.google.android.gms.tasks.Task
import com.google.android.gms.tasks.TaskCompletionSource
import kotlinx.coroutines.experimental.CancellationException
import kotlinx.coroutines.experimental.CompletableDeferred
import kotlinx.coroutines.experimental.Deferred
import kotlinx.coroutines.experimental.Job
import kotlinx.coroutines.experimental.suspendCancellableCoroutine

/**
 * Converts this deferred value to the instance of [Task].
 */
public fun <T> Deferred<T>.asTask(): Task<T> {
    val cancellation = CancellationTokenSource()
    val source = TaskCompletionSource<T>(cancellation.token)

    invokeOnCompletion callback@{
        if (isCancelled) {
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
 */
public fun <T> Task<T>.asDeferred(): Deferred<T> {
    if (isComplete) {
        val e = exception
        return if (e == null) {
            CompletableDeferred<T>().apply { if (isCanceled) cancel() else complete(result) }
        } else {
            CompletableDeferred<T>().apply { completeExceptionally(e) }
        }
    }

    val result = CompletableDeferred<T>()

    addOnCompleteListener {
        val e = it.exception
        if (e == null) {
            if (isCanceled) result.cancel() else result.complete(it.result)
        } else {
            result.completeExceptionally(e)
        }
    }

    return result
}

/**
 * Awaits for completion of the task without blocking a thread.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * stops waiting for the completion stage and immediately resumes with [CancellationException].
 */
public suspend fun <T> Task<T>.await(): T {
    if (isComplete) {
        val e = exception
        return if (e == null) {
            if (isCanceled) {
                throw CancellationException("Task $this was cancelled normally.")
            } else {
                result
            }
        } else {
            throw e
        }
    }

    return suspendCancellableCoroutine { cont ->
        addOnCompleteListener {
            val e = exception
            if (e == null) {
                if (isCanceled) cont.cancel() else cont.resume(result)
            } else {
                cont.resumeWithException(e)
            }
        }
    }
}
