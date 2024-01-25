package benchmarks.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*

@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 1)
@BenchmarkMode(Mode.Throughput)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)
open class CombineFlowsBenchmark {

    @Param("10", "100", "1000")
    private var size = 10

    @Benchmark
    fun combine() = runBlocking {
        combine((1 until size).map { flowOf(it) }) { a -> a}.collect()
    }

    @Benchmark
    fun combineTransform() = runBlocking {
        val list = (1 until size).map { flowOf(it) }.toList()
        combineTransform((1 until size).map { flowOf(it) }) { emit(it) }.collect()
    }
}

