package benchmarks.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*
import kotlin.coroutines.*

@Warmup(iterations = 5, time = 1)
@Measurement(iterations = 5, time = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
@Fork(value = 2)
open class FlowOnThreadContextBenchmark {

    @Param("none", "element", "flowOnOnly", "outerWithContext")
    private var contextMode = "none"

    private val size = 1000
    private val threadLocal = ThreadLocal<Int>()
    private lateinit var outerContext: CoroutineContext
    private lateinit var flowOnContext: CoroutineContext

    @Setup
    fun setup() {
        outerContext = if (contextMode == "none" || contextMode == "flowOnOnly") EmptyCoroutineContext else threadLocal.asContextElement(1)
        flowOnContext = if (contextMode == "none") CoroutineName("upstream") else threadLocal.asContextElement(2)
    }

    private fun source(suspendInUpstream: Boolean) = flow {
        for (i in 0 until size) {
            emit(i)
            if (suspendInUpstream) yield()
        }
    }

    private suspend fun collect(suspendInUpstream: Boolean, suspendInCollector: Boolean): Int {
        var sum = 0
        source(suspendInUpstream).flowOn(flowOnContext).collect {
            sum += it
            if (suspendInCollector) yield()
        }
        return sum
    }

    private fun run(suspendInUpstream: Boolean, suspendInCollector: Boolean): Int =
        if (contextMode == "outerWithContext") {
            runBlocking { withContext(outerContext) { collect(suspendInUpstream, suspendInCollector) } }
        } else {
            runBlocking(outerContext) { collect(suspendInUpstream, suspendInCollector) }
        }

    @Benchmark
    fun noSuspension(): Int = run(suspendInUpstream = false, suspendInCollector = false)

    @Benchmark
    fun suspendInUpstream(): Int = run(suspendInUpstream = true, suspendInCollector = false)

    @Benchmark
    fun suspendInCollector(): Int = run(suspendInUpstream = false, suspendInCollector = true)
}

@Warmup(iterations = 5, time = 1)
@Measurement(iterations = 5, time = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
@Fork(value = 2)
open class WithContextThreadContextBenchmark {

    private val size = 1000
    private val threadLocal = ThreadLocal<Int>()
    private val element = threadLocal.asContextElement(1)

    @Benchmark
    fun withContextPerIterationNoSuspension(): Int = runBlocking {
        var sum = 0
        repeat(size) { withContext(element) { sum += it } }
        sum
    }

    @Benchmark
    fun withContextPerIterationYield(): Int = runBlocking {
        var sum = 0
        repeat(size) { withContext(element) { yield(); sum += it } }
        sum
    }

    @Benchmark
    fun yieldInsideWithContext(): Int = runBlocking {
        var sum = 0
        withContext(element) { repeat(size) { yield(); sum += it } }
        sum
    }
}
