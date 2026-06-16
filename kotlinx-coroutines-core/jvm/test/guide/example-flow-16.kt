// This file was automatically generated from coroutines-flow-operators.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.exampleFlow16

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

fun simple(): Flow<Int> = (1..3).asFlow()

fun main() = runBlocking<Unit> {
    simple()
        .onCompletion { println("Done") }
        .collect { value -> println(value) }
}            
