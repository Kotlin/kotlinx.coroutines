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
open class ChannelNanoBenchmarkUnlimited {
    @Param(value = ["0", "100000", "1000000", "10000000", "100000000"])  // 0, 400 KB, 4, 40, 400 MB
    private var prefill = 0

    lateinit var channel: Channel<Int>

    @Setup(Level.Trial)
    fun createPrefilledChannel() {
        channel = Channel(Channel.UNLIMITED)
        repeat(prefill) {
            channel.trySend(it)
        }
    }

    @Benchmark
    fun sendReceive() = runBlocking {
        channel.send(42)
        return@runBlocking channel.receive()
    }
}
