/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.Segment
import kotlinx.coroutines.selects.*

/**
 * All waiters (such as [CancellableContinuationImpl] and [SelectInstance]) in synchronization and
 * communication primitives, should implement this interface to make the code faster and easier to read.
 */
internal interface Waiter {
    /**
     * When this waiter is cancelled, [Segment.onCancellation] with
     * the specified [segment] and [index] should be called.
     * This function installs the corresponding cancellation handler.
     */
    fun invokeOnCancellation(segment: Segment<*>, index: Int)
}
