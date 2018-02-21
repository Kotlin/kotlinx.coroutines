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

import kotlin.coroutines.experimental.*
import kotlin.internal.*

/**
 * Receiver interface for generic coroutine builders, so that the code inside coroutine has a convenient
 * and fast access to its own cancellation status via [isActive].
 */
public interface CoroutineScope {
    /**
     * Returns `true` when this coroutine is still active (has not completed and was not cancelled yet).
     *
     * Check this property in long-running computation loops to support cancellation:
     * ```
     * while (isActive) {
     *     // do some computation
     * }
     * ```
     *
     * This property is a shortcut for `coroutineContext.isActive` in the scope when
     * [CoroutineScope] is available.
     * See [coroutineContext][kotlin.coroutines.experimental.coroutineContext],
     * [isActive][kotlinx.coroutines.experimental.isActive] and [Job.isActive].
     */
    public val isActive: Boolean

    /**
     * Returns the context of this coroutine.
     *
     * @suppress: **Deprecated**: Replaced with top-level [kotlin.coroutines.experimental.coroutineContext].
     */
    @Deprecated("Replace with top-level coroutineContext",
        replaceWith = ReplaceWith("coroutineContext",
            imports = ["kotlin.coroutines.experimental.coroutineContext"]))
    @LowPriorityInOverloadResolution
    @Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE")
    public val coroutineContext: CoroutineContext
}