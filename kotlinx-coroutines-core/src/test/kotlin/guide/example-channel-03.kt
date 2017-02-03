// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package guide.channel.example03

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*

fun produceSquares() = buildChannel<Int>(CommonPool) {
    for (x in 1..5) send(x * x)
}

fun main(args: Array<String>) = runBlocking<Unit> {
    val squares = produceSquares()
    for (y in squares) println(y)
    println("Done!")
}
