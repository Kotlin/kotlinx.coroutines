// This file was automatically generated from Delay.kt by Knit tool. Do not edit.
package kotlinx.coroutines.examples.exampleDelayDuration02

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
}.debounce {
    if (it == 1) {
        0.milliseconds
    } else {
        1000.milliseconds
    }
}
.toList().joinToString().let { println(it) } }
