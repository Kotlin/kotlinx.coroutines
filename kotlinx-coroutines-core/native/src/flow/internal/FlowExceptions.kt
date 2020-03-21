/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

internal actual class AbortFlowException actual constructor(
    actual val owner: FlowCollector<*>
) : CancellationException("Flow was aborted, no more elements needed")
internal actual class ChildCancelledException : CancellationException("Child of the scoped flow was cancelled")

