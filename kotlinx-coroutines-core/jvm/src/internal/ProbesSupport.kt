/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("NOTHING_TO_INLINE", "INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")

package kotlinx.coroutines.internal

import kotlin.coroutines.*
import kotlin.coroutines.jvm.internal.probeCoroutineCreated as probe

internal actual inline fun <T> probeCoroutineCreated(completion: Continuation<T>): Continuation<T> = probe(completion)
