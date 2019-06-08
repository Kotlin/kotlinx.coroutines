/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.*

/**
 * This exception is thrown when operator need no more elements from the flow.
 * This exception should never escape outside of operator's implementation.
 */
internal expect class AbortFlowException() : CancellationException

/**
 * Exception used to cancel child of [scopedFlow] without cancelling the whole scope.
 */
internal expect class ChildCancelledException() : CancellationException
