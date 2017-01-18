package examples

import kotlinx.coroutines.experimental.*

val receiverThread = newSingleThreadContext("ReceiverThread")

fun main(args: Array<String>) = runBlocking(Here) {
    val va = Array<Deferred<String>>(10) { i ->
        defer(CommonPool) {
            val sleepTime = i * 200L
            log("This value #$i will delay for $sleepTime ms before producing result")
            try {
                delay(sleepTime)
                log("Value $i is producing result!")
            } catch (ex: Exception) {
                log("Value $i was aborted because of $ex")
            }
            "Result #$i"
        }
    }
    log("Created ${va.size} values")
    try {
        withTimeout(1100L) {
            run(receiverThread) {
                for (v in va)
                    log("Got value: ${v.await()}")
            }
        }
    } finally {
        log("The receiver thread is still active = ${receiverThread[Job.Key]!!.isActive}")
    }
}
