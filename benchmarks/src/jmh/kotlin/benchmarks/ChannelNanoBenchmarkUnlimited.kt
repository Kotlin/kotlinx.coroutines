package benchmarks

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*

/**
 * Benchmarks with `runBlocking` are significantly skewed by `runBlocking` overhead.
 */
@Warmup(iterations = 5, time = 1)
@Measurement(iterations = 5, time = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@Fork(1)
open class ChannelNanoBenchmarkUnlimited {
    @State(Scope.Benchmark)
    open class PrefilledChannelState {
        private val list = List(10_000_000) { it }

        @Param(value = ["0", "100000", "1000000", "10000000"])  // 0, 400 KB, 4, 40 MB
        private var prefill = 0

        lateinit var channel: Channel<Int>

        @Setup(Level.Trial)
        fun createPrefilledChannel() {
            channel = Channel(Channel.UNLIMITED)
            repeat(prefill) {
                channel.trySend(list[it])
            }
        }
    }

    @Benchmark
    fun sendReceive(s: PrefilledChannelState): Int = runBlocking {
        s.channel.send(42)
        return@runBlocking s.channel.receive()
    }

    @Benchmark
    fun trySendTryReceive(s: PrefilledChannelState): Int {
        s.channel.trySend(42)
        return s.channel.tryReceive().getOrThrow()
    }

    @State(Scope.Benchmark)
    open class EmptyChannelState {
        lateinit var channel: Channel<Int>

        @Setup(Level.Iteration)
        fun createEmptyChannel() {
            channel = Channel(Channel.UNLIMITED)
        }
    }

    @Benchmark
    fun send(s: EmptyChannelState) = runBlocking {
        s.channel.send(42)
    }

    @Benchmark
    fun trySend(s: EmptyChannelState) {
        s.channel.trySend(42)
    }

    @State(Scope.Benchmark)
    open class BigChannelState {
        private val list = List(100_000_000) { it }
        lateinit var channel: Channel<Int>

        @Setup(Level.Iteration)
        fun createPrefilledChannel() {
            channel = Channel(Channel.UNLIMITED)
            for (it in list) {
                channel.trySend(it)
            }
        }
    }

    @Benchmark
    fun receive(s: BigChannelState): Int = runBlocking {
        return@runBlocking s.channel.receive()
    }

    @Benchmark
    fun tryReceive(s: BigChannelState): Int {
        return s.channel.tryReceive().getOrThrow()
    }
}
