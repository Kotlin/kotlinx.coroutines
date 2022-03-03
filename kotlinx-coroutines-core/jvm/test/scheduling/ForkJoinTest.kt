/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.scheduling

import kotlinx.coroutines.*
import org.junit.*
import java.util.concurrent.*
import kotlin.coroutines.*

class ForkJoinTest : SchedulerTestBase() {
    companion object {
        /*
         * Change task size to control global granularity of benchmark
         * Change batch size to control affinity/work stealing/scheduling overhead effects
         */
        const val TASK_SIZE = 8192 * 1024
        const val BATCH_SIZE = 32 * 8192
    }

    @Test
    fun asyncGoBased() {
        val coefficients = LongArray(TASK_SIZE) { ThreadLocalRandom.current().nextLong(0, 1024 * 1024) }
        println("kek")
        dispatcher.dispatch(EmptyCoroutineContext, Runnable {
            runBlocking {
                launch { startAsync(coefficients, 0, coefficients.size).await() }
            }
        })

        Thread.sleep(10000)

        assert(false)
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

    class RecursiveAction(
        val coefficients: LongArray, val start: Int, val end: Int, @Volatile var result: Double = 0.0,
        parent: RecursiveAction? = null
    ) : CountedCompleter<Double>(parent) {

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