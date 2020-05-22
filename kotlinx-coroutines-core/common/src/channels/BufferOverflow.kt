/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*

/**
 * A strategy for buffer overflow handling in [channels][Channel] and [flows][kotlinx.coroutines.flow.Flow] that
 * controls behavior on buffer overflow and typically defaults to [SUSPEND].
 */
@ExperimentalCoroutinesApi
public enum class BufferOverflow {
    /**
     * Suspend on buffer overflow.
     */
    SUSPEND,

    /**
     * Keep latest value on buffer overflow, drop oldest, do not suspend.
     */
    KEEP_LATEST,

    /**
     * Drop latest value on buffer overflow, keep oldest, do not suspend.
     */
    DROP_LATEST
}
