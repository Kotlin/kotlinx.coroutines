// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package guide.channel.example05

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import kotlin.coroutines.experimental.CoroutineContext

fun numbersFrom(context: CoroutineContext, start: Int) = buildChannel<Int>(context) {
    var x = start
    while (true) send(x++) // infinite stream of integers from start
}

fun filter(context: CoroutineContext, numbers: ReceiveChannel<Int>, prime: Int) = buildChannel<Int>(context) {
    for (x in numbers) if (x % prime != 0) send(x)
}

fun main(args: Array<String>) = runBlocking<Unit> {
    var cur = numbersFrom(context, 2)
    for (i in 1..10) {
        val prime = cur.receive()
        println(prime)
        cur = filter(context, cur, prime)
    }
}
