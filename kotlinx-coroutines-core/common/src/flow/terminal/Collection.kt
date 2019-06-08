/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.jvm.*

/**
 * Collects given flow into a [destination]
 */
@ExperimentalCoroutinesApi
public suspend fun <T> Flow<T>.toList(destination: MutableList<T> = ArrayList()): List<T> = toCollection(destination)

/**
 * Collects given flow into a [destination]
 */
@ExperimentalCoroutinesApi
public suspend fun <T> Flow<T>.toSet(destination: MutableSet<T> = LinkedHashSet()): Set<T> = toCollection(destination)

/**
 * Collects given flow into a [destination]
 */
@ExperimentalCoroutinesApi
public suspend fun <T, C : MutableCollection<in T>> Flow<T>.toCollection(destination: C): C {
    collect { value ->
        destination.add(value)
    }
    return destination
}
