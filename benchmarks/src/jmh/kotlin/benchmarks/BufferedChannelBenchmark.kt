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
@Fork(1)
open class BufferedChannelBenchmark {
    @Param("1", "2")
    var capacity: Int = 0

    @Benchmark
    fun channelPipeline(): Int = runBlocking {
        run(Dispatchers.IO.limitedParallelism(3))
    }

    private suspend inline fun run(context: CoroutineContext): Int =
        Channel.range(100_000, context)
            .filter(context) { it % 4 == 0 }
            .fold(0) { a, b -> a + b }

    private fun Channel.Factory.range(count: Int, context: CoroutineContext) = GlobalScope.produce(context, capacity) {
        for (i in 0 until count)
            send(i)
    }

    // Migrated from deprecated operators, are good only for stressing channels

    private fun ReceiveChannel<Int>.filter(context: CoroutineContext = Dispatchers.Unconfined, predicate: suspend (Int) -> Boolean): ReceiveChannel<Int> =
        GlobalScope.produce(context, onCompletion = { cancel() }) {
            for (e in this@filter) {
                if (predicate(e)) send(e)
            }
        }

    private suspend inline fun <E, R> ReceiveChannel<E>.fold(initial: R, operation: (acc: R, E) -> R): R {
        var accumulator = initial
        consumeEach {
            accumulator = operation(accumulator, it)
        }
        return accumulator
    }
}