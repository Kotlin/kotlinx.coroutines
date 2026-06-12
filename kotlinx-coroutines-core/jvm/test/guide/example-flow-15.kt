// This file was automatically generated from coroutines-flow-operators.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.exampleFlow15

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

fun simple(): Flow<Int> = (1..3).asFlow()

fun main() = runBlocking<Unit> {
    try {
        simple().collect { value -> println(value) }
    } finally {
        println("Done")
    }
}            
