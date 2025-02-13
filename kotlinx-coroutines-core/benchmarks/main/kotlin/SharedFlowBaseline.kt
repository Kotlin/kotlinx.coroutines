package kotlinx.coroutines

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlinx.benchmark.*

// Stresses out 'syncrhonozed' codepath in MutableSharedFlow
@State(Scope.Benchmark)
@Measurement(iterations = 3, time = 1, timeUnit = BenchmarkTimeUnit.SECONDS)
@OutputTimeUnit(BenchmarkTimeUnit.MICROSECONDS)
@BenchmarkMode(Mode.AverageTime)
open class SharedFlowBaseline {
    private var size: Int = 10_000

    @Benchmark
    fun baseline() = runBlocking {
        val flow = MutableSharedFlow<Unit>()
        launch {
            repeat(size) { flow.emit(Unit) }
        }

        flow.take(size).collect {  }
    }
}
