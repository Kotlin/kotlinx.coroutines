// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package guide.channel.example06

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*

fun produceNumbers() = buildChannel<Int>(CommonPool) {
    var x = 1 // start from 1
    while (true) {
        send(x++) // produce next
        delay(100) // wait 0.1s
    }
}

fun launchProcessor(id: Int, channel: ReceiveChannel<Int>) = launch(CommonPool) {
    while (true) {
        val x = channel.receive()
        println("Processor #$id received $x")
    }
}

fun main(args: Array<String>) = runBlocking<Unit> {
    val producer = produceNumbers()
    repeat(5) { launchProcessor(it, producer) }
    delay(1000)
    producer.cancel() // cancel producer coroutine and thus kill them all
}
