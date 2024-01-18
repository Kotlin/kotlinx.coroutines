// This file was automatically generated from Delay.kt by Knit tool. Do not edit.
package kotlinx.coroutines.examples.exampleDelay03

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.time.Duration.Companion.milliseconds

fun main() = runBlocking {

flow {
    repeat(10) {
        emit(it)
        delay(110)
    }
}.sample(200)
.toList().joinToString().let { println(it) } }
