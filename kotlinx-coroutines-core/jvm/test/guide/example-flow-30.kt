// This file was automatically generated from flow.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.exampleFlow30

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

fun simple(): Flow<Int> = flow {
    for (i in 1..3) {
        println("Emitting $i")
        emit(i)
    }
}

fun main() = runBlocking<Unit> {
    simple()
        .onEach { value ->
            check(value <= 1) { "Collected $value" }                 
            println(value) 
        }
        .catch { e -> println("Caught $e") }
        .collect()
}            
