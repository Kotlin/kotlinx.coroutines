/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from Delay.kt by Knit tool. Do not edit.
package kotlinx.coroutines.examples.exampleDelayDuration01

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.time.Duration.Companion.milliseconds

fun main() = runBlocking {

flow {
    emit(1)
    delay(90.milliseconds)
    emit(2)
    delay(90.milliseconds)
    emit(3)
    delay(1010.milliseconds)
    emit(4)
    delay(1010.milliseconds)
    emit(5)
}.debounce(1000.milliseconds)
.toList().joinToString().let { println(it) } }
