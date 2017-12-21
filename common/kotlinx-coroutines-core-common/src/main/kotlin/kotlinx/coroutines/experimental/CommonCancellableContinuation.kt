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

import kotlin.coroutines.experimental.Continuation

public expect interface CancellableContinuation<in T> : Continuation<T> {
    public val isActive: Boolean
    public val isCompleted: Boolean
    public val isCancelled: Boolean
    @Suppress("EXPECTED_DECLARATION_WITH_DEFAULT_PARAMETER")
    public fun tryResume(value: T, idempotent: Any? = null): Any?
    public fun completeResume(token: Any)
    public fun initCancellability()
    @Suppress("EXPECTED_DECLARATION_WITH_DEFAULT_PARAMETER")
    public actual fun cancel(cause: Throwable? = null): Boolean
    public fun invokeOnCompletion(handler: CompletionHandler): DisposableHandle
    public fun CoroutineDispatcher.resumeUndispatched(value: T)
    public fun CoroutineDispatcher.resumeUndispatchedWithException(exception: Throwable)
}

@Suppress("EXPECTED_DECLARATION_WITH_DEFAULT_PARAMETER")
public expect suspend fun <T> suspendCancellableCoroutine(
    holdCancellability: Boolean = false,
    block: (CancellableContinuation<T>) -> Unit
): T

@Suppress("EXPECTED_DECLARATION_WITH_DEFAULT_PARAMETER")
public expect suspend fun <T> suspendAtomicCancellableCoroutine(
    holdCancellability: Boolean = false,
    block: (CancellableContinuation<T>) -> Unit
): T
