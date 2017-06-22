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

@PublishedApi internal const val MODE_ATOMIC_DEFAULT = 0 // schedule non-cancellable dispatch for suspendCoroutine
@PublishedApi internal const val MODE_CANCELLABLE = 1    // schedule cancellable dispatch for suspendCancellableCoroutine
@PublishedApi internal const val MODE_DIRECT = 2         // when the context is right just invoke the delegate continuation direct
@PublishedApi internal const val MODE_UNDISPATCHED = 3   // when the thread is right, but need to mark it with current coroutine

fun <T> Continuation<T>.resumeMode(value: T, mode: Int) {
    when (mode) {
        MODE_ATOMIC_DEFAULT -> resume(value)
        MODE_CANCELLABLE -> resumeCancellable(value)
        MODE_DIRECT -> resumeDirect(value)
        MODE_UNDISPATCHED -> (this as DispatchedContinuation).resumeUndispatched(value)
        else -> error("Invalid mode $mode")
    }
}

fun <T> Continuation<T>.resumeWithExceptionMode(exception: Throwable, mode: Int) {
    when (mode) {
        MODE_ATOMIC_DEFAULT -> resumeWithException(exception)
        MODE_CANCELLABLE -> resumeCancellableWithException(exception)
        MODE_DIRECT -> resumeDirectWithException(exception)
        MODE_UNDISPATCHED -> (this as DispatchedContinuation).resumeUndispatchedWithException(exception)
        else -> error("Invalid mode $mode")
    }
}
