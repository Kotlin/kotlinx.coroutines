/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlinx.coroutines.experimental.NonCancellable.isActive
import kotlinx.coroutines.experimental.selects.*
import kotlin.coroutines.experimental.*

/**
 * A non-cancelable job that is always [active][isActive]. It is designed for [withContext] function
 * to prevent cancellation of code blocks that need to be executed without cancellation.
 *
 * Use it like this:
 * ```
 * withContext(NonCancellable) {
 *     // this code will not be cancelled
 * }
 * ```
 */
public object NonCancellable : AbstractCoroutineContextElement(Job), Job {
    /** Always returns `true`. */
    override val isActive: Boolean  get() = true

    /** Always returns `false`. */
    override val isFailed: Boolean get() = false

    /** Always returns `false`. */
    override val isCompleted: Boolean get() = false

    /** Always returns `false`. */
    override val isCancelled: Boolean get() = false

    /** Always returns `false`. */
    override fun start(): Boolean = false

    /** Always throws [UnsupportedOperationException]. */
    override suspend fun join() {
        throw UnsupportedOperationException("This job is always active")
    }

    override val onJoin: SelectClause0
        get() = throw UnsupportedOperationException("This job is always active")

    /** Always throws [IllegalStateException]. */
    override fun getCancellationException(): CancellationException = throw IllegalStateException("This job is always active")

    /** Always returns [NonDisposableHandle]. */
    @Suppress("OverridingDeprecatedMember")
    override fun invokeOnCompletion(handler: CompletionHandler): DisposableHandle =
        NonDisposableHandle

    /** Always returns [NonDisposableHandle]. */
    @Suppress("OverridingDeprecatedMember")
    override fun invokeOnCompletion(handler: CompletionHandler, onCancelling: Boolean): DisposableHandle =
        NonDisposableHandle

    /** Always returns [NonDisposableHandle]. */
    @Suppress("OverridingDeprecatedMember")
    override fun invokeOnCompletion(onCancelling_: Boolean, handler: CompletionHandler): DisposableHandle =
        NonDisposableHandle

    /** Always returns [NonDisposableHandle]. */
    override fun invokeOnCompletion(onFailing: Boolean, invokeImmediately: Boolean, handler: CompletionHandler): DisposableHandle =
        NonDisposableHandle

    /** Always returns `false`. */
    override fun cancel(cause: Throwable?): Boolean = false // never handles exceptions

    /** @suppress */
    override fun childFailed(cause: Throwable): Boolean = false // never handles exceptions

    /** @suppress */
    override fun cancelChild(parentJob: Job): Unit = error("Cannot be invoked, does not have a parent")

    /** Always returns [emptySequence]. */
    override val children: Sequence<Job>
        get() = emptySequence()

    /** Always returns [NonDisposableHandle] and does not do anything. */
    @Suppress("OverridingDeprecatedMember")
    override fun attachChild(child: Job): DisposableHandle = NonDisposableHandle

    /** Does not do anything. */
    @Suppress("OverridingDeprecatedMember")
    override fun cancelChildren(cause: Throwable?) {}
}
