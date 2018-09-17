/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("unused", "UNUSED_PARAMETER")

package kotlinx.coroutines

import kotlin.coroutines.*

@JvmName("probeCoroutineResumed")
internal fun probeCoroutineResumedNoOp(frame: Continuation<*>) = Unit
@JvmName("probeCoroutineSuspended")
internal fun probeCoroutineSuspendedNoOp(frame: Continuation<*>) = Unit
@JvmName("probeCoroutineCreated")
internal fun <T> probeCoroutineCreatedNoOp(completion: kotlin.coroutines.Continuation<T>): kotlin.coroutines.Continuation<T> = completion
