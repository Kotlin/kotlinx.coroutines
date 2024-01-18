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
}.timeout(100.milliseconds).catch { exception ->
    if (exception is TimeoutCancellationException) {
        // Catch the TimeoutCancellationException emitted above.
        // Emit desired item on timeout.
        emit(-1)
    } else {
        // Throw other exceptions.
        throw exception
    }
}.onEach {
    delay(300) // This will not cause a timeout
}
.toList().joinToString().let { println(it) } }
