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
import kotlin.coroutines.experimental.CoroutineContext

/**
 * Abstract class for coroutines.
 *
 *  * Coroutines implement completion [Continuation], [Job], and [CoroutineScope] interfaces.
 *  * Coroutine stores the result of continuation in the state of the job.
 *  * Coroutine waits for children coroutines to finish before completing.
 *  * Coroutines are cancelled through an intermediate _cancelling_ state.
 *
 * @param active when `true` coroutine is created in _active_ state, when `false` in _new_ state. See [Job] for details.
 * @suppress **This is unstable API and it is subject to change.**
 */
public abstract class AbstractCoroutine<in T>(
    private val parentContext: CoroutineContext,
    active: Boolean
) : JobSupport(active), Continuation<T>, CoroutineScope {
    @Suppress("LeakingThis")
    public final override val context: CoroutineContext = parentContext + this
    public final override val coroutineContext: CoroutineContext get() = context

    protected open val defaultResumeMode: Int get() = MODE_ATOMIC_DEFAULT

    final override fun resume(value: T) {
        makeCompletingOnce(value, defaultResumeMode)
    }

    final override fun resumeWithException(exception: Throwable) {
        makeCompletingOnce(CompletedExceptionally(exception), defaultResumeMode)
    }

    final override fun handleException(exception: Throwable) {
        handleCoroutineException(parentContext, exception)
    }
}

