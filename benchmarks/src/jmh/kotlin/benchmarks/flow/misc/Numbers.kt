/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */


package benchmarks.flow.misc

import benchmarks.flow.scrabble.flow
import io.reactivex.*
import io.reactivex.functions.*
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*

/*
 * Results:
 *
 * // Throw FlowAborted overhead
 * Numbers.primes             avgt    7  4106.837 ± 59.672  us/op
 * Numbers.primesRx           avgt    7  2777.232 ± 85.357  us/op
 *
 * // On par
 * Numbers.transformations    avgt    7    20.290 ±  1.367  us/op
 * Numbers.transformationsRx  avgt    7    22.932 ±  1.863  us/op
 *
 * // Channels overhead
 * Numbers.zip                avgt    7   470.737 ± 10.838  us/op
 * Numbers.zipRx              avgt    7   104.811 ±  9.073  us/op
 *
 */
@Warmup(iterations = 7, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 7, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
open class Numbers {

    companion object {
        private const val primes = 100
        private const val natural = 1000
    }

    private fun numbers() = flow {
        for (i in 2L..Long.MAX_VALUE) emit(i)
    }

    private fun primesFlow(): Flow<Long> = flow {
        var source = numbers()
        while (true) {
            val next = source.take(1).single()
            emit(next)
            source = source.filter { it % next != 0L }
        }
    }

    private fun rxNumbers() =
        Flowable.generate(Callable { 1L }, BiFunction<Long, Emitter<Long>, Long> { state, emitter ->
            val newState = state + 1
            emitter.onNext(newState)
            newState
        })

    private fun generateRxPrimes(): Flowable<Long> = Flowable.generate(Callable { rxNumbers() },
        BiFunction<Flowable<Long>, Emitter<Long>, Flowable<Long>> { state, emitter ->
            // Not the most fair comparison, but here we go
            val prime = state.firstElement().blockingGet()
            emitter.onNext(prime)
            state.filter { it % prime != 0L }
        })

    @Benchmark
    fun primes() = runBlocking {
        primesFlow().take(primes).count()
    }

    @Benchmark
    fun primesRx() = generateRxPrimes().take(primes.toLong()).count().blockingGet()

    @Benchmark
    fun zip() = runBlocking {
        val numbers = numbers().take(natural)
        val first = numbers
            .filter { it % 2L != 0L }
            .map { it * it }
        val second = numbers
            .filter { it % 2L == 0L }
            .map { it * it }
        first.zip(second) { v1, v2 -> v1 + v2 }.filter { it % 3 == 0L }.count()
    }

    @Benchmark
    fun zipRx() {
        val numbers = rxNumbers().take(natural.toLong())
        val first = numbers
            .filter { it % 2L != 0L }
            .map { it * it }
        val second = numbers
            .filter { it % 2L == 0L }
            .map { it * it }
        first.zipWith(second, BiFunction<Long, Long, Long> { v1, v2 -> v1 + v2 }).filter { it % 3 == 0L }.count()
            .blockingGet()
    }

    @Benchmark
    fun transformations(): Int = runBlocking {
        numbers()
            .take(natural)
            .filter { it % 2L != 0L }
            .map { it * it }
            .filter { (it + 1) % 3 == 0L }.count()
    }

    @Benchmark
    fun transformationsRx(): Long {
       return rxNumbers().take(natural.toLong())
            .filter { it % 2L != 0L }
            .map { it * it }
            .filter { (it + 1) % 3 == 0L }.count()
            .blockingGet()
    }
}
