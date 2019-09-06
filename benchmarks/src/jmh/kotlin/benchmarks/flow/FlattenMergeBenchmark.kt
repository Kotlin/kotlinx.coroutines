package benchmarks.flow

import benchmarks.doWork
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.ThreadLocalRandom
import java.util.concurrent.TimeUnit
import kotlin.math.ceil

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

    /**
     * Number of flows that are merged in this benchmark. Negative number means that number of flows
     * will be computed as -([flows] * [concurrency]), positive number will be chosen as number of flows.
     */
    @Param("-10", "-1", "100", "500")
    private var flows: Int = 0

    @Param("1", "2", "4") // local machine
//    @Param("1", "2", "4", "8", "16", "32", "64", "128", "144") // dasquad
//    @Param("1", "2", "4", "8", "16", "32", "64", "96") // Google Cloud
    private var concurrency: Int = 0

    private lateinit var flow: Flow<Flow<Int>>

    @Setup
    fun setup() {
        val flowsNumber = if (flows >= 0) flows else -(flows * concurrency)
        val flowElementsToProcess = ceil(ELEMENTS / flowsNumber.toDouble())

        flow = (1..flowsNumber).asFlow().map {
            flow {
                repeat(flowElementsToProcess.toInt()) {
                    doWork(WORK)
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

private const val ELEMENTS = 100_000
private const val WORK = 80