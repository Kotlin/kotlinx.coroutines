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
    /**
     * Always returns `true`.
     * @suppress **This an internal API and should not be used from general code.**
     */
    @InternalCoroutinesApi
    override val isActive: Boolean  get() = true

    /**
     * Always returns `false`.
     * @suppress **This an internal API and should not be used from general code.**
     */
    @InternalCoroutinesApi
    override val isCompleted: Boolean get() = false

    /**
     * Always returns `false`.
     * @suppress **This an internal API and should not be used from general code.**
     */
    @InternalCoroutinesApi
    override val isCancelled: Boolean get() = false

    /**
     * Always returns `false`.
     * @suppress **This an internal API and should not be used from general code.**
     */
    @InternalCoroutinesApi
    override fun start(): Boolean = false

    /**
     * Always throws [UnsupportedOperationException].
     * @suppress **This an internal API and should not be used from general code.**
     */
    @InternalCoroutinesApi
    override suspend fun join() {
        throw UnsupportedOperationException("This job is always active")
    }

    /**
     * Always throws [UnsupportedOperationException].
     * @suppress **This an internal API and should not be used from general code.**
     */
    override val onJoin: SelectClause0
        get() = throw UnsupportedOperationException("This job is always active")

    /**
     * Always throws [IllegalStateException].
     * @suppress **This an internal API and should not be used from general code.**
     */
    @InternalCoroutinesApi
    override fun getCancellationException(): CancellationException = throw IllegalStateException("This job is always active")

    /**
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Suppress("OverridingDeprecatedMember")
    @InternalCoroutinesApi
    override fun invokeOnCompletion(handler: CompletionHandler): DisposableHandle =
        NonDisposableHandle

    /**
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Suppress("OverridingDeprecatedMember")
    @InternalCoroutinesApi
    @Deprecated(message = "For binary compatibility", level = DeprecationLevel.HIDDEN)
    override fun invokeOnCompletion(handler: CompletionHandler, onCancelling: Boolean): DisposableHandle =
        NonDisposableHandle

    /**
     * Always returns no-op handle.
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Suppress("OverridingDeprecatedMember")
    @InternalCoroutinesApi
    @Deprecated(message = "Use with named `onCancellation` and `handler` parameters", level = DeprecationLevel.WARNING,
        replaceWith = ReplaceWith("this.invokeOnCompletion(onCancellation = onCancelling_, handler = handler)"))
    override fun invokeOnCompletion(onCancelling_: Boolean, handler: CompletionHandler): DisposableHandle =
        NonDisposableHandle

    /**
     * Always returns no-op handle.
     * @suppress **This an internal API and should not be used from general code.**
     */
    @InternalCoroutinesApi
    override fun invokeOnCompletion(onCancelling: Boolean, invokeImmediately: Boolean, handler: CompletionHandler): DisposableHandle =
        NonDisposableHandle

    /**
     * Always returns `false`.
     * @suppress **This an internal API and should not be used from general code.**
     */
    @InternalCoroutinesApi
    override fun cancel(): Boolean = false

    /**
     * Always returns `false`.
     * @suppress **This an internal API and should not be used from general code.**
     */
    @InternalCoroutinesApi
    override fun cancel(cause: Throwable?): Boolean = false // never handles exceptions

    /**
     * Always returns [emptySequence].
     * @suppress **This an internal API and should not be used from general code.**
     */
    @InternalCoroutinesApi
    override val children: Sequence<Job>
        get() = emptySequence()

    /**
     * Always returns [NonDisposableHandle] and does not do anything.
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Suppress("EXPOSED_FUNCTION_RETURN_TYPE", "EXPOSED_PARAMETER_TYPE")
    @InternalCoroutinesApi
    override fun attachChild(child: ChildJob): ChildHandle = NonDisposableHandle

    /**
     * Does not do anything.
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Suppress("OverridingDeprecatedMember")
    @InternalCoroutinesApi
    @Deprecated(message = "Binary compatibility, it is an extension now", level = DeprecationLevel.HIDDEN)
    override fun cancelChildren(cause: Throwable?) {}
}
