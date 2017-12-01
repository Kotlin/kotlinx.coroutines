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
public actual object NonCancellable : AbstractCoroutineContextElement(Job), Job {
    /** Always returns `true`. */
    actual override val isActive: Boolean  get() = true

    /** Always returns `false`. */
    actual override val isCompleted: Boolean get() = false

    /** Always returns `false`. */
    actual override val isCancelled: Boolean get() = false

    /** Always returns `false`. */
    actual override fun start(): Boolean = false

    /** Always throws [UnsupportedOperationException]. */
    actual suspend override fun join() {
        throw UnsupportedOperationException("This job is always active")
    }

    /** Always throws [IllegalStateException]. */
    actual override fun getCancellationException(): CancellationException = throw IllegalStateException("This job is always active")

    /** Always returns [NonDisposableHandle]. */
    actual override fun invokeOnCompletion(onCancelling: Boolean, invokeImmediately: Boolean, handler: CompletionHandler): DisposableHandle =
        NonDisposableHandle

    /** Always returns `false`. */
    actual override fun cancel(cause: Throwable?): Boolean = false

    /** Always returns [emptySequence]. */
    actual override val children: Sequence<Job>
        get() = emptySequence()

    /** Always returns [NonDisposableHandle] and does not do anything. */
    @Suppress("OverridingDeprecatedMember")
    actual override fun attachChild(child: Job): DisposableHandle = NonDisposableHandle
}
