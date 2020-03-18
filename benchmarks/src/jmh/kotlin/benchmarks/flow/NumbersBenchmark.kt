/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */


package benchmarks.flow

import benchmarks.flow.scrabble.flow
import io.reactivex.*
import io.reactivex.functions.*
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*

@Warmup(iterations = 7, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 7, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
open class NumbersBenchmark {

    companion object {
        private const val primes = 100
        private const val natural = 1000L
    }

    private fun numbers(limit: Long = Long.MAX_VALUE) = flow {
        for (i in 2L..limit) emit(i)
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
        val numbers = numbers(natural)
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
        numbers(natural)
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
