package benchmarks

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.openjdk.jmh.annotations.*
import org.openjdk.jmh.infra.Blackhole
import java.util.concurrent.*

/**
 * This is NOT a comprehensive channel benchmark suit.
 * It's a collection of rather arbitrary low-effort benchmarks.
 *
 * This collection does NOT measure:
 * - isolated `send` or `receive` performance
 * - typical channel usage patterns (they are unknown and need to be researched)
 *
 * These benchmarks are affected by:
 * - Initializing and maintaining structured concurrency overhead (`runBlocking`)
 * - Thread scheduling
 * - Internal channel structure, such as allocations
 * - GC
 * - Not necessarily hot-path performance
 * - Not necessarily typical usage patterns
 */
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

    @Param(value = ["1000", "10000", "100000", "1000000", "10000000"]) // 4, 40, 400 KB, 4, 40 MB
    var count: Int = 0

    // 1. Preallocate.
    // 2. Different values to avoid helping the cache.
    val list = List(100_000_000) { it }

    @State(Scope.Benchmark)
    open class PrefilledChannelState {
        @Param(value = ["0", "100000", "1000000", "10000000"]) // 0, 400 KB, 4, 40 MB
        private var prefill = 0

        lateinit var channel: Channel<Int>

        val list = List(100_000_000) { it }

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
    fun sendReceiveUnlimited(bh: Blackhole, s: PrefilledChannelState) = runBlocking {
        runSendReceive(bh, s.channel, count)
    }

    @Benchmark
    fun sendReceiveConflated(bh: Blackhole) = runBlocking(Dispatchers.Default) {
        runSendReceive(bh, Channel(Channel.CONFLATED), count)
    }

    @Benchmark
    fun sendReceiveRendezvous(bh: Blackhole) = runBlocking(Dispatchers.Default) {
        // NB: Rendezvous is partly benchmarking the scheduler, not the channel alone.
        // So don't trust the Rendezvous results too much.
        runSendReceive(bh, Channel(Channel.RENDEZVOUS), count)
    }

    @Benchmark
    fun oneSenderManyReceivers(bh: Blackhole, s: PrefilledChannelState) = runBlocking {
        runSendReceive(bh, s.channel, count, 1, cores - 1)
    }

    @Benchmark
    fun manySendersOneReceiver(bh: Blackhole, s: PrefilledChannelState) = runBlocking {
        runSendReceive(bh, s.channel, count, cores - 1, 1)
    }

    @Benchmark
    fun manySendersManyReceivers(bh: Blackhole, s: PrefilledChannelState) = runBlocking {
        runSendReceive(bh, s.channel, count, cores / 2, cores / 2)
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
    private suspend inline fun runSendReceive(bh: Blackhole, channel: Channel<Int>, count: Int, senders: Int = 1, receivers: Int = 1) {
        //require (senders > 0 && receivers > 0)
        //require (senders + receivers <= cores) // Can be used with more than num cores, but what would it measure?
        // If the channel is prefilled with N items, it should have (at least) N items by the end of the benchmark.
        // We roughly send as many items as we receive, within this function.
        val receiveAll = channel.isEmpty
        // send almost `count` items, up to `senders - 1` items will not be sent (negligible)
        val countPerSender = count / senders
        val countSent = countPerSender * senders
        // for prefilled channel only: up to `receivers - 1` number of items will not be received
        // (on top of the number of prefilled items, which we do not aim to receive at all) (negligible)
        val countPerReceiverAtLeast = countSent / receivers
        withContext(Dispatchers.Default) {
            repeat(receivers) {
                launch {
                    if (receiveAll) {
                        channel.forEach {
                            bh.consume(it)
                        }
                    } else {
                       repeat(countPerReceiverAtLeast) {
                           bh.consume(channel.receive())
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
