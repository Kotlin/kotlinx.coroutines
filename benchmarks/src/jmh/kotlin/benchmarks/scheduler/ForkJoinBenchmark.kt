/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.scheduler

import benchmarks.*
import kotlinx.coroutines.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*

/*
 * Comparison of fork-join tasks using specific FJP API and classic [async] jobs.
 * FJP job is organized in perfectly balanced binary tree, every leaf node computes
 * FPU-heavy sum over its data and intermediate nodes sum results.
 *
 * Fine-grained batch size (8192 * 1024 tasks, 128 in sequential batch)
 * ForkJoinBenchmark.asyncExperimental  avgt   10  681.512 ± 32.069  ms/op
 * ForkJoinBenchmark.asyncFjp           avgt   10  845.386 ± 73.204  ms/op
 * ForkJoinBenchmark.fjpRecursiveTask   avgt   10  692.120 ± 26.224  ms/op
 * ForkJoinBenchmark.fjpTask            avgt   10  791.087 ± 66.544  ms/op
 *
 * Too small tasks (8192 * 1024 tasks, 128 batch, 16 in sequential batch)
 * Benchmark                            Mode  Cnt     Score     Error  Units
 * ForkJoinBenchmark.asyncExperimental  avgt   10  1273.271 ± 190.372  ms/op
 * ForkJoinBenchmark.asyncFjp           avgt   10  1406.102 ± 216.793  ms/op
 * ForkJoinBenchmark.fjpRecursiveTask   avgt   10   849.941 ± 141.254  ms/op
 * ForkJoinBenchmark.fjpTask            avgt   10   831.554 ±  57.276  ms/op
 */
@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 2)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)
open class ForkJoinBenchmark : ParametrizedDispatcherBase() {

    companion object {
        /*
         * Change task size to control global granularity of benchmark
         * Change batch size to control affinity/work stealing/scheduling overhead effects
         */
        const val TASK_SIZE = 8192 * 1024
        const val BATCH_SIZE = 32 * 8192
    }

    lateinit var coefficients: LongArray
    override var dispatcher: String = "scheduler"

    @Setup
    override fun setup() {
        super.setup()
        coefficients = LongArray(TASK_SIZE) { ThreadLocalRandom.current().nextLong(0, 1024 * 1024) }
    }

    @Benchmark
    fun asyncFjp() = runBlocking {
        CoroutineScope(ForkJoinPool.commonPool().asCoroutineDispatcher()).startAsync(coefficients, 0, coefficients.size).await()
    }

    @Benchmark
    fun asyncExperimental() = runBlocking {
        startAsync(coefficients, 0, coefficients.size).await()
    }

    @Benchmark
    fun fjpRecursiveTask(): Double {
        val task = RecursiveAction(coefficients, 0, coefficients.size)
        return ForkJoinPool.commonPool().submit(task).join()
    }

    @Benchmark
    fun fjpTask(): Double {
        val task = Task(coefficients, 0, coefficients.size)
        return ForkJoinPool.commonPool().submit(task).join()
    }

    suspend fun CoroutineScope.startAsync(coefficients: LongArray, start: Int, end: Int): Deferred<Double> = async {
        if (end - start <= BATCH_SIZE) {
            compute(coefficients, start, end)
        } else {
            val first = startAsync(coefficients, start, start + (end - start) / 2)
            val second = startAsync(coefficients, start + (end - start) / 2, end)
            first.await() + second.await()
        }
    }

    class Task(val coefficients: LongArray, val start: Int, val end: Int) : RecursiveTask<Double>() {
        override fun compute(): Double {
            if (end - start <= BATCH_SIZE) {
                return compute(coefficients, start, end)
            }

            val first = Task(coefficients, start, start + (end - start) / 2).fork()
            val second = Task(coefficients, start + (end - start) / 2, end).fork()

            var result = 0.0
            result += first.join()
            result += second.join()
            return result
        }

        private fun compute(coefficients: LongArray, start: Int, end: Int): Double {
            var result = 0.0
            for (i in start until end) {
                result += Math.sin(Math.pow(coefficients[i].toDouble(), 1.1)) + 1e-8
            }

            return result
        }
    }

    class RecursiveAction(val coefficients: LongArray, val start: Int, val end: Int, @Volatile var result: Double = 0.0,
                          parent: RecursiveAction? = null) : CountedCompleter<Double>(parent) {

        private var first: ForkJoinTask<Double>? = null
        private var second: ForkJoinTask<Double>? = null

        override fun getRawResult(): Double {
            return result
        }

        override fun setRawResult(t: Double) {
            result = t
        }

        override fun compute() {
            if (end - start <= BATCH_SIZE) {
                rawResult = compute(coefficients, start, end)
            } else {
                pendingCount = 2
                // One may fork only once here and executing second task here with looping over firstComplete to be even more efficient
                first = RecursiveAction(
                    coefficients,
                    start,
                    start + (end - start) / 2,
                    parent = this
                ).fork()
                second = RecursiveAction(
                    coefficients,
                    start + (end - start) / 2,
                    end,
                    parent = this
                ).fork()
            }

            tryComplete()
        }

        override fun onCompletion(caller: CountedCompleter<*>?) {
            if (caller !== this) {
                rawResult = first!!.rawResult + second!!.rawResult
            }
            super.onCompletion(caller)
        }
    }
}


private fun compute(coefficients: LongArray, start: Int, end: Int): Double {
    var result = 0.0
    for (i in start until end) {
        result += Math.sin(Math.pow(coefficients[i].toDouble(), 1.1)) + 1e-8
    }

    return result
}