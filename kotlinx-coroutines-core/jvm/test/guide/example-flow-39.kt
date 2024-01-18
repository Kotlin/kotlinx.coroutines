// This file was automatically generated from flow.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.exampleFlow39

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

fun main() = runBlocking<Unit> {
    (1..5).asFlow().cancellable().collect { value -> 
        if (value == 3) cancel()  
        println(value)
    } 
}
