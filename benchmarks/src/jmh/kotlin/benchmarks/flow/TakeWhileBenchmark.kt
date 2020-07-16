/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")

package benchmarks.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.flow.internal.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.TimeUnit

@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
open class TakeWhileBenchmark {
    @Param("1", "10", "100", "1000")
    private var size: Int = 0

    private suspend inline fun Flow<Long>.consume() =
        filter { it % 2L != 0L }
            .map { it * it }.count()

    @Benchmark
    fun baseline() = runBlocking<Int> {
        (0L until size).asFlow().consume()
    }

    @Benchmark
    fun takeWhileDirect() = runBlocking<Int> {
        (0L..Long.MAX_VALUE).asFlow().takeWhileDirect { it < size }.consume()
    }

    @Benchmark
    fun takeWhileViaCollectWhile() = runBlocking<Int> {
        (0L..Long.MAX_VALUE).asFlow().takeWhileViaCollectWhile { it < size }.consume()
    }

    // Direct implementation by checking predicate and throwing AbortFlowException
    private fun <T> Flow<T>.takeWhileDirect(predicate: suspend (T) -> Boolean): Flow<T> = unsafeFlow {
        try {
            collect { value ->
                if (predicate(value)) emit(value)
                else throw AbortFlowException(this)
            }
        } catch (e: AbortFlowException) {
            e.checkOwnership(owner = this)
        }
    }

    // Essentially the same code, but reusing the logic via collectWhile function
    private fun <T> Flow<T>.takeWhileViaCollectWhile(predicate: suspend (T) -> Boolean): Flow<T> = unsafeFlow {
        // This return is needed to work around a bug in JS BE: KT-39227
        return@unsafeFlow collectWhile { value ->
            if (predicate(value)) {
                emit(value)
                true
            } else {
                false
            }
        }
    }
}
