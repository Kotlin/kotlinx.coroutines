/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.CoroutineContext

expect public interface Job : CoroutineContext.Element {
    public companion object Key : CoroutineContext.Key<Job>
    public val isActive: Boolean
    public val isCompleted: Boolean
    public val isCancelled: Boolean
    public fun getCancellationException(): CancellationException
    public fun start(): Boolean
    @Suppress("EXPECTED_DECLARATION_WITH_DEFAULT_PARAMETER")
    public fun cancel(cause: Throwable? = null): Boolean
    public val children: Sequence<Job>
    @Deprecated(message = "Start child coroutine with 'parent' parameter", level = DeprecationLevel.WARNING)
    public fun attachChild(child: Job): DisposableHandle
    public suspend fun join()
    @Suppress("EXPECTED_DECLARATION_WITH_DEFAULT_PARAMETER")
    public actual fun invokeOnCompletion(
        onCancelling: Boolean = false,
        invokeImmediately: Boolean = true,
        handler: CompletionHandler): DisposableHandle
}

@Suppress("FunctionName", "EXPECTED_DECLARATION_WITH_DEFAULT_PARAMETER")
public expect fun Job(parent: Job? = null): Job

public expect interface DisposableHandle {
    public fun dispose()
}

@Suppress("EXPECTED_DECLARATION_WITH_DEFAULT_PARAMETER")
public expect fun CoroutineContext.cancel(cause: Throwable? = null): Boolean
@Suppress("EXPECTED_DECLARATION_WITH_DEFAULT_PARAMETER")
public expect fun CoroutineContext.cancelChildren(cause: Throwable? = null)

public expect fun Job.disposeOnCompletion(handle: DisposableHandle): DisposableHandle
public expect suspend fun Job.cancelAndJoin()
@Suppress("EXPECTED_DECLARATION_WITH_DEFAULT_PARAMETER", "EXTENSION_SHADOWED_BY_MEMBER") // See KT-21598
public expect fun Job.cancelChildren(cause: Throwable? = null)
public expect suspend fun Job.joinChildren()

public expect object NonDisposableHandle : DisposableHandle {
    override fun dispose()
}

internal expect open class JobSupport(active: Boolean) : Job {
    public final override val key: CoroutineContext.Key<*>
    public final override val isActive: Boolean
    public final override val isCompleted: Boolean
    public final override val isCancelled: Boolean

    public final override fun getCancellationException(): CancellationException
    public final override fun start(): Boolean
    public final override val children: Sequence<Job>

    public override fun cancel(cause: Throwable?): Boolean

    public final override fun attachChild(child: Job): DisposableHandle
    public final override suspend fun join()

    // todo: non-final as a workaround for KT-21968, should be final in the future
    public override fun invokeOnCompletion(
        onCancelling: Boolean,
        invokeImmediately: Boolean,
        handler: CompletionHandler
    ): DisposableHandle

    public val isCompletedExceptionally: Boolean
    public fun getCompletionExceptionOrNull(): Throwable?

    internal fun initParentJobInternal(parent: Job?)
    internal fun makeCompletingOnce(proposedUpdate: Any?, mode: Int): Boolean
    internal open fun hasOnFinishingHandler(update: Any?): Boolean
    internal open fun onFinishingInternal(update: Any?)
    internal open fun onCompletionInternal(state: Any?, mode: Int)
    internal open fun onStartInternal()
    internal open fun onCancellationInternal(exceptionally: CompletedExceptionally?)
    internal open fun nameString(): String
    internal open fun handleException(exception: Throwable)
}