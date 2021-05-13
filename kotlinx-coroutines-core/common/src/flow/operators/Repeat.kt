/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlin.jvm.*

/**
 * The [repeat] operator allows you to repeat an emission multiples times.
 * (similar RxJava repeat operator)
 * For example:
 * ```kotlin
 * flow {
 *     emit(1)
 * }.repeat(3)
 * ```
 * produces the following emissions
 * ```text
 * 1, 1, 1
 * ```
 * */
public fun <T> Flow<T>.repeat(times: Int): Flow<T> = flow {
    repeat (times) { emitAll(this@repeat) }
}

/**
 * Similar to [repeat] operator, the [repeatUntil] allows you to repeat an emission
 * until the provided [condition] returns true.
 *
 * (similar RxJava repeatUntil operator)
 * */
public fun <T> Flow<T>.repeatUntil(condition: () -> Boolean): Flow<T> = flow {
    while(!condition()) { emitAll(this@repeatUntil) }
}
