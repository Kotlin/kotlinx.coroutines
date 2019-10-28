/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.flow.*

internal object NopCollector : FlowCollector<Any?> {
    override suspend fun emit(value: Any?) {
        // does nothing
    }
}