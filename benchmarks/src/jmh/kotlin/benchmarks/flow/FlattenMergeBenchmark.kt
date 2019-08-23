package benchmarks.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.consumesAll
import kotlinx.coroutines.flow.*
import org.openjdk.jmh.annotations.*
import org.openjdk.jmh.infra.Blackhole
import java.util.concurrent.TimeUnit

/**
 * This benchmark can be considered as a macro benchmark for the [kotlinx.coroutines.sync.Semaphore]
 */
@Warmup(iterations = 5)
@Measurement(iterations = 10)
@BenchmarkMode(Mode.Throughput)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
@Fork(1)
open class FlattenMergeBenchmark {

    @Param("-10", "-1", "100", "500")
    private var flows: Int = 0

    @Param("1", "2", "4") // local machine
//    @Param("1", "2", "4", "8", "16", "32", "64", "128", "144") // dasquad
//    @Param("1", "2", "4", "8", "16", "32", "64", "96") // Google Cloud
    private var concurrency: Int = 0

    private lateinit var flow: Flow<Flow<Int>>

    @Setup
    fun setup() {
        val flowsCount = if (flows < 0) {
            -flows * concurrency
        }
        else {
            flows
        }

        flow = (1..flowsCount).asFlow().map {
            flow {
                repeat(ELEMENTS / flowsCount) {
                    emit(it)
                }
            }
        }
    }

    @Benchmark
    fun flattenMerge() = runBlocking {
        flow.flattenMerge(concurrency = concurrency).collect()
    }
}

private const val ELEMENTS = 100