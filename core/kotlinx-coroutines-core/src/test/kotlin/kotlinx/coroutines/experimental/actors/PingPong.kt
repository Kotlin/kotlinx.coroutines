package kotlinx.coroutines.experimental.actors

import kotlinx.coroutines.experimental.*


class Ping(private val pong: Pong) : TypedActor<Ping>() {

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

class Pong : TypedActor<Pong>() {
    suspend fun onPing(counter: Int, sender: Ping): Unit = act {
        sender.onPong(counter + 1)
    }
}

fun main(args: Array<String>) = runBlocking {
    val pong = Pong()
    val ping = Ping(pong)
    ping.start()
    ping.join()
}