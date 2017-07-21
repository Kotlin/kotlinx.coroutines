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

import kotlinx.coroutines.experimental.NonCancellable.isActive
import kotlinx.coroutines.experimental.selects.SelectInstance
import kotlin.coroutines.experimental.AbstractCoroutineContextElement

/**
 * A non-cancelable job that is always [active][isActive]. It is designed to be used with [run] builder
 * to prevent cancellation of code blocks that need to run without cancellation.
 *
 * Use it like this:
 * ```
 * run(NonCancellable) {
 *     // this code will not be cancelled
 * }
 * ```
 */
object NonCancellable : AbstractCoroutineContextElement(Job), Job {
    /** Always returns `true`. */
    override val isActive: Boolean  get() = true

    /** Always returns `false`. */
    override val isCompleted: Boolean get() = false

    /** Always returns `false`. */
    override val isCancelled: Boolean get() = false

    /** Always returns `false`. */
    override fun start(): Boolean = false

    /** Always throws [UnsupportedOperationException]. */
    suspend override fun join() {
        throw UnsupportedOperationException("This job is always active")
    }

    /**
     * Always throws [UnsupportedOperationException].
     * @suppress **This is unstable API and it is subject to change.**
     */
    override fun <R> registerSelectJoin(select: SelectInstance<R>, block: suspend () -> R)  {
        throw UnsupportedOperationException("This job is always active")
    }

    /** Always throws [IllegalStateException]. */
    override fun getCompletionException(): CancellationException = throw IllegalStateException("This job is always active")

    /** Always returns [NonDisposableHandle]. */
    override fun invokeOnCompletion(handler: CompletionHandler): DisposableHandle = NonDisposableHandle

    /** Always returns [NonDisposableHandle]. */
    override fun invokeOnCompletion(handler: CompletionHandler, onCancelling: Boolean): DisposableHandle = NonDisposableHandle

    /** Always returns `false`. */
    override fun cancel(cause: Throwable?): Boolean = false
}
