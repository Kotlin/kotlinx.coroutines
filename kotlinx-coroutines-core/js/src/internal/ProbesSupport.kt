/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlin.coroutines.*

@Suppress("NOTHING_TO_INLINE")
internal actual inline fun <T> probeCoroutineCreated(completion: Continuation<T>): Continuation<T> = completion
