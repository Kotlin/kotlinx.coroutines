// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package guide.channel.example01

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*

fun main(args: Array<String>) = runBlocking<Unit> {
    val channel = Channel<Int>()
    launch(CommonPool) {
        // this might be heavy CPU-consuming computation or async logic, we'll just send five squares
        for (x in 1..5) channel.send(x * x)
    }
    // here we print five received integers:
    repeat(5) { println(channel.receive()) }
    println("Done!")
}
