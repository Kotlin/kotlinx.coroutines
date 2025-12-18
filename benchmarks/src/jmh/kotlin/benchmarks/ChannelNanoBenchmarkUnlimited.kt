package benchmarks

import kotlinx.coroutines.channels.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*

@Warmup(iterations = 30, time = 1)
@Measurement(iterations = 30, time = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@Fork(1)
open class ChannelNanoBenchmarkUnlimited {
    @State(Scope.Benchmark)
    open class PrefilledChannelState {
        private val list = List(1_000_000) { it }

        @Param(value = ["0", "10000", "100000", "1000000"])  // 0, 40, 400 KB, 4 MB
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
    fun trySendTryReceive(s: PrefilledChannelState): Int {
        s.channel.trySend(42)
        return s.channel.tryReceive().getOrThrow()
    }
}
