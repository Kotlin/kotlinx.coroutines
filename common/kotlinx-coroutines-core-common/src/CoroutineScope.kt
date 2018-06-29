/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
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