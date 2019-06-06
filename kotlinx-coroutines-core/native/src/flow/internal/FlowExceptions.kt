/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.*

internal actual class AbortFlowException : CancellationException("Flow was aborted, no more elements needed")
internal actual class ChildCancelledException : CancellationException("Child of the scoped flow was cancelled")

