package benchmarks.examples

import org.openjdk.jmh.annotations.*
import java.util.concurrent.TimeUnit

@Warmup(iterations = 10, time = 1)
@Measurement(iterations = 10, time = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@Fork(1)
open class ListBenchmark {
    @State(Scope.Benchmark)
    open class PrefilledList {
        @Param("0", "100000", "1000000", "10000000")
        var prefill = 0

        val lst: MutableList<Int> = mutableListOf(42)

        @Setup(Level.Iteration)
        fun setup() {
            repeat(prefill) { lst.add(it) }
        }
    }

    @Benchmark
    fun add(s: PrefilledList) {
        s.lst.add(42)
    }

    @State(Scope.Benchmark)
    open class PrefilledReusableList {
        @Param("0", "100000", "1000000", "10000000")
        var prefill = 0

        val lst: MutableList<Int> = mutableListOf(42)

        @Setup(Level.Trial)
        fun setup() {
            repeat(prefill) { lst.add(it) }
        }
    }

    @Benchmark
    fun addRemoveLast(s: PrefilledReusableList) {
        s.lst.add(42)
        s.lst.removeLast()
    }
}
