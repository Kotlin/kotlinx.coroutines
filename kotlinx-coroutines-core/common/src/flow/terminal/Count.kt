/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.jvm.*

/**
 * Returns the number of elements in this flow.
 */
@ExperimentalCoroutinesApi
public suspend fun <T> Flow<T>.count(): Int  {
    var i = 0
    collect {
        ++i
    }

    return i
}

/**
 * Returns the number of elements matching the given predicate.
 */
@ExperimentalCoroutinesApi
public suspend fun <T> Flow<T>.count(predicate: suspend (T) -> Boolean): Int  {
    var i = 0
    collect { value ->
        if (predicate(value)) {
            ++i
        }
    }

    return i
}
