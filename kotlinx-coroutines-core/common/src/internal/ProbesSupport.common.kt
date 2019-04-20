/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlin.coroutines.*

internal expect inline fun <T> probeCoroutineCreated(completion: Continuation<T>): Continuation<T>
