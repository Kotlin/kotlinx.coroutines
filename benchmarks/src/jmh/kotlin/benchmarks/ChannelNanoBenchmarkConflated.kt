package benchmarks

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*

@Warmup(iterations = 5, time = 1)
@Measurement(iterations = 5, time = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@State(Scope.Benchmark)
@Fork(1)
open class ChannelNanoBenchmarkConflated {
    var channel: Channel<Int> = Channel(Channel.CONFLATED)

    @Benchmark
    fun send() = runBlocking {
        channel.send(42)
    }

    @Benchmark
    fun trySend() {
        channel.trySend(42)
    }

    @Benchmark
    fun sendReceive(): Int = runBlocking {
        channel.send(42)
        return@runBlocking channel.receive()
    }

    @Benchmark
    fun trySendTryReceive(): Int {
        channel.trySend(42)
        return channel.tryReceive().getOrThrow()
    }
}
