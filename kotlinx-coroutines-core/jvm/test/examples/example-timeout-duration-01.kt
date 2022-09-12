/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from Delay.kt by Knit tool. Do not edit.
package kotlinx.coroutines.examples.exampleTimeoutDuration01

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.time.Duration.Companion.milliseconds

fun main() = runBlocking {

flow {
    emit(1)
    delay(100)
    emit(2)
    delay(100)
    emit(3)
    delay(1000)
    emit(4)
}.timeout(100.milliseconds).catch {
    emit(-1) // Item to emit on timeout
}.onEach {
    delay(300) // This will not cause a timeout
}
.toList().joinToString().let { println(it) } }
