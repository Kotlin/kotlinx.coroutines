/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.unsafeFlow as flow
import kotlin.jvm.*

/**
 * Delays the emission of values from this flow for the given [timeMillis].
 */
@FlowPreview
public fun <T> Flow<T>.delayFlow(timeMillis: Long): Flow<T> = flow {
    delay(timeMillis)
    collect { value ->
        emit(value)
    }
}

/**
 * Delays each element emitted by the given flow for the given [timeMillis].
 */
@FlowPreview
public fun <T> Flow<T>.delayEach(timeMillis: Long): Flow<T> = flow {
    collect { value ->
        delay(timeMillis)
        emit(value)
    }
}
