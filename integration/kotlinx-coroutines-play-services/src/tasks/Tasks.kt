/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("RedundantVisibilityModifier")

package kotlinx.coroutines.experimental.tasks

import com.google.android.gms.tasks.OnCompleteListener
import com.google.android.gms.tasks.RuntimeExecutionException
import com.google.android.gms.tasks.Task
import com.google.android.gms.tasks.TaskCompletionSource
import kotlinx.coroutines.experimental.CancellationException
import kotlinx.coroutines.experimental.CompletableDeferred
import kotlinx.coroutines.experimental.Deferred
import kotlinx.coroutines.experimental.Job
import kotlinx.coroutines.experimental.suspendCancellableCoroutine
import java.util.concurrent.Executor

/**
 * Converts this deferred value to the instance of [Task].
 */
public fun <T> Deferred<T>.asTask(): Task<T> = TaskCompletionSource<T>().apply {
    invokeOnCompletion {
        try {
            setResult(getCompleted())
        } catch (e: Exception) {
            setException(e)
        } catch (t: Throwable) {
            setException(RuntimeExecutionException(t))
        }
    }
}.task

/**
 * Converts this task to an instance of [Deferred].
 */
public fun <T> Task<T>.asDeferred(executor: Executor? = null): Deferred<T> {
    if (isComplete) {
        val e = exception
        return if (e == null) {
            CompletableDeferred<T>().apply { if (isCanceled) cancel() else complete(result) }
        } else {
            CompletableDeferred<T>().apply { completeExceptionally(e) }
        }
    }

    val result = CompletableDeferred<T>()
    val listener = OnCompleteListener<T> {
        val e = it.exception
        if (e == null) {
            if (isCanceled) result.cancel() else result.complete(it.result)
        } else {
            result.completeExceptionally(e)
        }
    }

    if (executor == null) {
        addOnCompleteListener(listener)
    } else {
        addOnCompleteListener(executor, listener)
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
public suspend fun <T> Task<T>.await(executor: Executor? = null): T {
    if (isComplete) {
        val e = exception
        return if (e == null) {
            if (isCanceled) throw CancellationException() else result
        } else {
            throw e
        }
    }

    return suspendCancellableCoroutine { cont ->
        val listener = OnCompleteListener<T> {
            val e = exception
            if (e == null) {
                if (isCanceled) cont.cancel() else cont.resume(result)
            } else {
                cont.resumeWithException(e)
            }
        }

        if (executor == null) {
            addOnCompleteListener(listener)
        } else {
            addOnCompleteListener(executor, listener)
        }
    }
}
