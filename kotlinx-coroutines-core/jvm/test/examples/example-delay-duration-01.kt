@file:OptIn(ExperimentalTime::class)
/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from Delay.kt by Knit tool. Do not edit.
package kotlinx.coroutines.examples.exampleDelayDuration01

import kotlin.time.*
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

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
