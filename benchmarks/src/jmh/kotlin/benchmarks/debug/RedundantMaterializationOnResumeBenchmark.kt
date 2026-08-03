package benchmarks.debug

import kotlinx.coroutines.*
import kotlinx.coroutines.debug.*
import org.openjdk.jmh.annotations.*
import org.openjdk.jmh.annotations.State
import java.util.concurrent.*
import java.util.concurrent.atomic.AtomicInteger

// IJPL-251805, KT-57634
@Warmup(iterations = 5, time = 1)
@Measurement(iterations = 5, time = 1)
@Fork(value = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
open class RedundantMaterializationOnResumeBenchmark {

    @Volatile
    private var sink = 42 // prevent TCO

    @Param("1", "10", "50")
    private var depth: Int = 1

    @Param("true", "false")
    var withDebugger = false

    @Setup
    fun setup() {
        DebugProbes.sanitizeStackTraces = false
        DebugProbes.enableCreationStackTraces = false
        if (withDebugger) {
            DebugProbes.install()
        }
    }

    @Benchmark
    fun suspendFewTimes() = runBlocking {
        repeat(100) {
            recursion(depth)
            sink = 239
        }
    }


    suspend fun recursion(depth: Int) {
        if (depth - 1 == 0) {
            stateMachine()
            sink = 42
            return
        }
        recursion(depth - 1)
        sink = 42
    }

    private suspend fun stateMachine() {
        yield()
        sink = 42
    }
}
