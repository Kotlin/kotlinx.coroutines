@file:OptIn(ExperimentalTime::class)
/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from Delay.kt by Knit tool. Do not edit.
package kotlinx.coroutines.examples.exampleDelayDuration03

import kotlin.time.*
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

fun main() = runBlocking {

flow {
    repeat(10) {
        emit(it)
        delay(110.milliseconds)
    }
}.sample(200.milliseconds)
.toList().joinToString().let { println(it) } }
