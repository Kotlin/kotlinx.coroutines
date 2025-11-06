package benchmarks

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*

@Warmup(iterations = 7, time = 1)
@Measurement(iterations = 10, time = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@State(Scope.Benchmark)
@Fork(1)
open class ChannelBenchmark {
    // max coroutines launched per benchmark
    // to allow for true parallelism
    val cores = Runtime.getRuntime().availableProcessors()

    //                4 KB,   40 KB,   400 KB,      4 MB,      40 MB,      400 MB
    @Param(value = ["1000", "10000", "100000", "1000000", "10000000", "100000000"])
    var count: Int = 0

    // 1. Preallocate.
    // 2. Different values to avoid helping the cache.
    val list = List(100000000) { it }

    @State(Scope.Benchmark)
    open class UnlimitedChannelWrapper {
        //                0,      4 MB,      40 MB,      400 MB
        @Param("0", "1000000", "10000000", "100000000")
        private var prefill = 0

        lateinit var channel: Channel<Int>

        val list = List(100000000) { it }

        @Setup(Level.Invocation)
        fun createPrefilledChannel() {
            channel = Channel(Channel.UNLIMITED)
            repeat(prefill) {
                channel.trySend(list[it])
            }
        }
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
    fun sendReceiveUnlimited(wrapper: UnlimitedChannelWrapper) = runBlocking {
        runSendReceive(wrapper.channel, count)
    }

    @Benchmark
    fun sendReceiveConflated() = runBlocking(Dispatchers.Default) {
        runSendReceive(Channel(Channel.CONFLATED), count)
    }

    @Benchmark
    fun sendReceiveRendezvous() = runBlocking(Dispatchers.Default) {
        // NB: Rendezvous is partly benchmarking the scheduler, not the channel alone.
        // So don't trust the Rendezvous results too much.
        runSendReceive(Channel(Channel.RENDEZVOUS), count)
    }

    @Benchmark
    fun oneSenderManyReceivers(wrapper: UnlimitedChannelWrapper) = runBlocking {
        runSendReceive(wrapper.channel, count, 1, cores - 1)
    }

    @Benchmark
    fun manySendersOneReceiver(wrapper: UnlimitedChannelWrapper) = runBlocking {
        runSendReceive(wrapper.channel, count, cores - 1, 1)
    }

    @Benchmark
    fun manySendersManyReceivers(wrapper: UnlimitedChannelWrapper) = runBlocking {
        runSendReceive(wrapper.channel, count, cores / 2, cores / 2)
    }

    private suspend fun runSend(count: Int, capacity: Int) {
        val channel = Channel<Int>(capacity)
        repeat(count) {
            channel.send(list[it])
        }
    }

    suspend fun <E> Channel<E>.forEach(action: (E) -> Unit) {
        for (element in this) {
            action(element)
        }
    }

    // NB: not all parameter combinations make sense in general.
    // E.g., for the rendezvous channel, senders should be equal to receivers.
    // If they are non-equal, it's a special case of performance under contention.
    private suspend inline fun runSendReceive(channel: Channel<Int>, count: Int, senders: Int = 1, receivers: Int = 1) {
        //require (senders > 0 && receivers > 0)
        //require (senders + receivers <= cores) // Can be used with more than num cores, but what would it measure?
        // if the channel is prefilled, only receive the items that were sent by this function
        val receiveAll = channel.isEmpty
        // send almost `count` items, up to `senders - 1` items will not be sent (negligible)
        val countPerSender = count / senders
        // for prefilled channel only: up to `receivers - 1` items of the sent items will not be received
        // (on top of the prefilled items which we do not aim to receive at all) (negligible)
        val countPerReceiverAtLeast = countPerSender * senders / receivers
        withContext(Dispatchers.Default) {
            repeat(receivers) {
                launch {
                    if (receiveAll) {
                        channel.forEach {
                            // possibly receive into the blackhole
                        }
                    } else {
                       repeat(countPerReceiverAtLeast) {
                           // possibly receive into the blackhole
                           channel.receive()
                       }
                    }
                }
            }

            coroutineScope {
                repeat(senders) {
                    launch {
                        repeat(countPerSender) {
                            channel.send(list[it])
                        }
                    }
                }
            }
            channel.close()
        }
    }
}
