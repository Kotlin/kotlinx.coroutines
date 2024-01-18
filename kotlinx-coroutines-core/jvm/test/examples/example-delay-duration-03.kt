// This file was automatically generated from Delay.kt by Knit tool. Do not edit.
package kotlinx.coroutines.examples.exampleDelayDuration03

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.time.Duration.Companion.milliseconds

fun main() = runBlocking {

flow {
    repeat(10) {
        emit(it)
        delay(110.milliseconds)
    }
}.sample(200.milliseconds)
.toList().joinToString().let { println(it) } }
