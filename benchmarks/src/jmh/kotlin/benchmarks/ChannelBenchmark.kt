package benchmarks

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*

@Warmup(iterations = 7, time = 1)
@Measurement(iterations = 10, time = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)
@Fork(1)
open class ChannelBenchmark {
    // max coroutines launched per benchmark
    // to allow for true parallelism
    val cores = 4

    //                4 KB,   40 KB,   400 KB,      4 MB,      40 MB,      400 MB
    @Param("1000", "10000", "100000", "1000000", "10000000", "100000000")
    var count: Int = 0

    // 1. Preallocate.
    // 2. Different values to avoid helping the cache.
    val list = ArrayList<Int>(100000000).apply {
        repeat(100000000) { add(it) }
    }

    @Benchmark
    fun sendUnlimited() = runBlocking {
        runSend(count, Channel.UNLIMITED)
    }

    @Benchmark
    fun sendConflated() = runBlocking {
        runSend(count, Channel.CONFLATED)
    }

    @Benchmark
    fun sendReceiveUnlimited() = runBlocking(Dispatchers.Default) {
        runSendReceive(count, Channel.UNLIMITED)
    }

    @Benchmark
    fun sendReceiveConflated() = runBlocking(Dispatchers.Default) {
        runSendReceive(count, Channel.CONFLATED)
    }

    @Benchmark
    fun sendReceiveRendezvous() = runBlocking(Dispatchers.Default) {
        // NB: Rendezvous is partly benchmarking the scheduler, not the channel alone.
        // So don't trust the Rendezvous results too much.
        runSendReceive(count, Channel.RENDEZVOUS)
    }

    @Benchmark
    fun oneSenderManyReceivers() = runBlocking {
        runSendReceive(count, Channel.UNLIMITED, 1, cores - 1)
    }

    @Benchmark
    fun manySendersOneReceiver() = runBlocking {
        runSendReceive(count, Channel.UNLIMITED, cores - 1, 1)
    }

    @Benchmark
    fun manySendersManyReceivers() = runBlocking {
        runSendReceive(count, Channel.UNLIMITED, cores / 2, cores / 2)
    }

    private suspend fun sendManyItems(count: Int, channel: Channel<Int>) = coroutineScope {
        for (i in 1..count) {
            channel.send(list[i])
        }
    }

    private suspend fun runSend(count: Int, capacity: Int) {
        Channel<Int>(capacity).also {
            sendManyItems(count, it)
        }
    }

    // NB: not all parameter combinations make sense in general.
    // E.g., for the rendezvous channel, senders should be equal to receivers.
    // If they are non-equal, it's a special case of performance under contention.
    private suspend inline fun runSendReceive(count: Int, capacity: Int, senders: Int = 1, receivers: Int = 1) {
        require(senders > 0 && receivers > 0)
        require(senders + receivers <= cores)
        withContext(Dispatchers.Default) {
            val channel = Channel<Int>(capacity)
            repeat(receivers) {
                launch {
                    channel.consumeEach { }
                }
            }

            coroutineScope {
                repeat(senders) {
                    launch {
                        sendManyItems(count / senders, channel)
                    }
                }
            }
            channel.close()
        }
    }
}
