package benchmarks.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.TimeUnit
import kotlin.coroutines.*

@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
open class UndispatchedFlowOnBenchmark {
    @Param("1", "10", "100", "1000")
    private var size: Int = 0

    private suspend inline fun Flow<Long>.consume() =
        filter { it % 2L != 0L }
            .map { it * it }.count()

    @Benchmark
    fun baseline() = runBlocking<Int> {
        (0L until size).asFlow().consume()
    }

    @Benchmark
    fun flowOn() = runBlocking<Int> {
        (0L until size).asFlow().flowOn(CoroutineName("name")).consume()
    }
}

