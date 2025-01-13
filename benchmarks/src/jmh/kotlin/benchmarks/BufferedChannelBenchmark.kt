package benchmarks

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*
import kotlin.coroutines.*

@Warmup(iterations = 7, time = 1)
@Measurement(iterations = 5, time = 1)
@BenchmarkMode(Mode.Throughput, Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
@Threads(3)
@Fork(1)
open class BufferedChannelBenchmark {
    @Param("1", "2")
    var capacity: Int = 0

    @Benchmark
    fun channelPipeline(): Int = runBlocking {
        run(Dispatchers.Unconfined)
    }

    private suspend inline fun run(context: CoroutineContext) =
        Channel
            .range(100_000, context)
            .fold(0) { a, b -> a + b }

    private fun Channel.Factory.range(count: Int, context: CoroutineContext) = GlobalScope.produce(context, capacity) {
        for (i in 0 until count)
            send(i)
    }

    // Migrated from deprecated operators, are good only for stressing channels

    private suspend inline fun <E, R> ReceiveChannel<E>.fold(initial: R, operation: (acc: R, E) -> R): R {
        var accumulator = initial
        consumeEach {
            accumulator = operation(accumulator, it)
        }
        return accumulator
    }
}