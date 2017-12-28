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

public expect class CompletionHandlerException(message: String, cause: Throwable) : RuntimeException

public open expect class CancellationException(message: String) : IllegalStateException

public expect class JobCancellationException(
    message: String,
    cause: Throwable?,
    job: Job
) : CancellationException {
    val job: Job
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
