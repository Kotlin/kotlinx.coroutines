/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

/**
 * A job that can be completed using [complete()] function.
 * It is returned by [Job()][Job] and [SupervisorJob()][SupervisorJob] constructor functions.
 */
public interface CompletableJob : Job {
    /**
     * Completes this job. The result is `true` if this job was completed as a result of this invocation and
     * `false` otherwise (if it was already completed).
     *
     * Subsequent invocations of this function have no effect and always produce `false`.
     *
     * This function transitions this job into _completed- state if it was not completed or cancelled yet.
     * However, that if this job has children, then it transitions into _completing_ state and becomes _complete_
     * once all its children are [complete][isCompleted]. See [Job] for details.
     */
    public fun complete(): Boolean

    /**
     * Completes this job exceptionally with a given [exception]. The result is `true` if this job was
     * completed as a result of this invocation and `false` otherwise (if it was already completed).
     * [exception] parameter is used as an additional debug information that is not handled by any exception handlers.
     *
     * Subsequent invocations of this function have no effect and always produce `false`.
     *
     * This function transitions this job into _cancelled_ state if it was not completed or cancelled yet.
     * However, that if this job has children, then it transitions into _cancelling_ state and becomes _cancelled_
     * once all its children are [complete][isCompleted]. See [Job] for details.
     *
     * Its responsibility of the caller to properly handle and report the given [exception], all job's children will receive
     * a [CancellationException] with the [exception] as a cause for the sake of diagnostic.
     */
    public fun completeExceptionally(exception: Throwable): Boolean
}
