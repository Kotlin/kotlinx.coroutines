/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("DEPRECATION_ERROR")

package kotlinx.coroutines

import kotlinx.coroutines.selects.*
import kotlin.coroutines.*

/**
 * A non-cancelable job that is always [active][Job.isActive]. It is designed for [withContext] function
 * to prevent cancellation of code blocks that need to be executed without cancellation.
 *
 * Use it like this:
 * ```
 * withContext(NonCancellable) {
 *     // this code will not be cancelled
 * }
 * ```
 *
 * **WARNING**: This object is not designed to be used with [launch], [async], and other coroutine builders.
 * if you write `launch(NonCancellable) { ... }` then not only the newly launched job will not be cancelled
 * when the parent is cancelled, the whole parent-child relation between parent and child is severed.
 * The parent will not wait for the child's completion, nor will be cancelled when the child crashed.
 */
@Suppress("DeprecatedCallableAddReplaceWith")
public object NonCancellable : AbstractCoroutineContextElement(Job), Job {

    private const val message = "NonCancellable can be used only as an argument for 'withContext', direct usages of its API are prohibited"

    /**
     * Always returns `true`.
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Deprecated(level = DeprecationLevel.WARNING, message = message)
    override val isActive: Boolean
        get() = true

    /**
     * Always returns `false`.
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Deprecated(level = DeprecationLevel.WARNING, message = message)
    override val isCompleted: Boolean get() = false

    /**
     * Always returns `false`.
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Deprecated(level = DeprecationLevel.WARNING, message = message)
    override val isCancelled: Boolean get() = false

    /**
     * Always returns `false`.
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Deprecated(level = DeprecationLevel.WARNING, message = message)
    override fun start(): Boolean = false

    /**
     * Always throws [UnsupportedOperationException].
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Deprecated(level = DeprecationLevel.WARNING, message = message)
    override suspend fun join() {
        throw UnsupportedOperationException("This job is always active")
    }

    /**
     * Always throws [UnsupportedOperationException].
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Deprecated(level = DeprecationLevel.WARNING, message = message)
    override val onJoin: SelectClause0
        get() = throw UnsupportedOperationException("This job is always active")

    /**
     * Always throws [IllegalStateException].
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Deprecated(level = DeprecationLevel.WARNING, message = message)
    override fun getCancellationException(): CancellationException = throw IllegalStateException("This job is always active")

    /**
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Deprecated(level = DeprecationLevel.WARNING, message = message)
    override fun invokeOnCompletion(handler: CompletionHandler): DisposableHandle =
        NonDisposableHandle

    /**
     * Always returns no-op handle.
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Deprecated(level = DeprecationLevel.WARNING, message = message)
    override fun invokeOnCompletion(onCancelling: Boolean, invokeImmediately: Boolean, handler: CompletionHandler): DisposableHandle =
        NonDisposableHandle

    /**
     * Does nothing.
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Deprecated(level = DeprecationLevel.WARNING, message = message)
    override fun cancel(cause: CancellationException?) {}

    /**
     * Always returns `false`.
     * @suppress This method has bad semantics when cause is not a [CancellationException]. Use [cancel].
     */
    @Deprecated(level = DeprecationLevel.HIDDEN, message = "Since 1.2.0, binary compatibility with versions <= 1.1.x")
    override fun cancel(cause: Throwable?): Boolean = false // never handles exceptions

    /**
     * Always returns [emptySequence].
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Deprecated(level = DeprecationLevel.WARNING, message = message)
    override val children: Sequence<Job>
        get() = emptySequence()

    /**
     * Always returns [NonDisposableHandle] and does not do anything.
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Deprecated(level = DeprecationLevel.WARNING, message = message)
    override fun attachChild(child: ChildJob): ChildHandle = NonDisposableHandle

    /** @suppress */
    override fun toString(): String {
        return "NonCancellable"
    }
}
