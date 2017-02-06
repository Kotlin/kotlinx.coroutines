// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package guide.context.example05

import kotlinx.coroutines.experimental.*

fun main(args: Array<String>) = runBlocking<Unit> {
    println("My job is ${context[Job]}")
}
