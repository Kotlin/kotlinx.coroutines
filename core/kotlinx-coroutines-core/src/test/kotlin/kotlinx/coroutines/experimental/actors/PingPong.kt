package kotlinx.coroutines.experimental.actors

import kotlinx.coroutines.experimental.*


class Ping(private val pong: Pong) : Actor() {

    suspend fun start() = act { pong.onPing(0, this) }

    suspend fun onPong(counter: Int): Unit = act {
        println("Received $counter")
        if (counter == 5) {
            pong.close()
            close()
        } else {
            pong.onPing(counter, this)
        }
    }
}

class Pong : Actor() {
    suspend fun onPing(counter: Int, sender: Ping): Unit = act {
        sender.onPong(counter + 1)
    }
}

data class Ball(val counter: Int, val sender: MonoActor<Int>)

fun main(args: Array<String>) = runBlocking {
    val pong = Pong()
    val ping = Ping(pong)
    ping.start()
    ping.join()

    println("Typed finished")

    val untypedPong = actor<Ball> {
        it.sender.send(it.counter + 1)
    }

    val untypedPing = actor<Int> {
        println("Received mono $it")
        if (it == 5) {
            untypedPong.close()
            close()
        } else {
            untypedPong.send(Ball(it, this))
        }
    }

    untypedPing.send(1)
    untypedPing.join()
}