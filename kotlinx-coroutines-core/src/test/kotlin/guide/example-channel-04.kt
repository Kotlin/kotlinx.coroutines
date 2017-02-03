// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package guide.channel.example04

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*

fun produceNumbers() = buildChannel<Int>(CommonPool) {
    var x = 1
    while (true) send(x++) // infinite stream of integers starting from 1
}

fun square(numbers: ReceiveChannel<Int>) = buildChannel<Int>(CommonPool) {
    for (x in numbers) send(x * x)
}

fun main(args: Array<String>) = runBlocking<Unit> {
    val numbers = produceNumbers() // produces integers from 1 and on
    val squares = square(numbers) // squares integers
    for (i in 1..5) println(squares.receive()) // print first five
    println("Done!") // we are done
    squares.cancel() // need to cancel these coroutines in a larger app
    numbers.cancel()
}
