package examples

import kotlinx.coroutines.experimental.future.await
import kotlinx.coroutines.experimental.runBlocking
import java.util.concurrent.CompletableFuture

fun main(args: Array<String>) {
    // Let's assume that we have a future coming from some 3rd party API
    val future: CompletableFuture<Int> = CompletableFuture.supplyAsync {
        Thread.sleep(1000L) // imitate some long-running computation, actually
        42
    }
    // now let's launch a coroutine and await for this future inside it
    runBlocking {
        println("We can do something else, while we are waiting for future...")
        println("We've got ${future.await()} from the future!")
    }
}