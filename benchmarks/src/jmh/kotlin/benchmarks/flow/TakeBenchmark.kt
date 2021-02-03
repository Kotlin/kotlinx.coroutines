/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.TimeUnit
import java.util.concurrent.CancellationException
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*
import benchmarks.flow.scrabble.flow as unsafeFlow

@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
open class TakeBenchmark {
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
    fun originalTake() = runBlocking<Int> {
        (0L..Long.MAX_VALUE).asFlow().originalTake(size).consume()
    }

    @Benchmark
    fun fastPathTake() = runBlocking<Int> {
        (0L..Long.MAX_VALUE).asFlow().fastPathTake(size).consume()
    }

    @Benchmark
    fun mergedStateMachine() = runBlocking<Int> {
        (0L..Long.MAX_VALUE).asFlow().mergedStateMachineTake(size).consume()
    }

    internal class StacklessCancellationException() : CancellationException() {
        override fun fillInStackTrace(): Throwable = this
    }

    public fun <T> Flow<T>.originalTake(count: Int): Flow<T> {
        return unsafeFlow {
            var consumed = 0
            try {
                collect { value ->
                    emit(value)
                    if (++consumed == count) {
                        throw StacklessCancellationException()
                    }
                }
            } catch (e: StacklessCancellationException) {
                // Nothing, bail out
            }
        }
    }

    private suspend fun <T> FlowCollector<T>.emitAbort(value: T) {
        emit(value)
        throw StacklessCancellationException()
    }

    public fun <T> Flow<T>.fastPathTake(count: Int): Flow<T> {
        return unsafeFlow {
            var consumed = 0
            try {
                collect { value ->
                    if (++consumed < count) {
                        return@collect emit(value)
                    } else {
                        return@collect emitAbort(value)
                    }
                }
            } catch (e: StacklessCancellationException) {
                // Nothing, bail out
            }
        }
    }


    public fun <T> Flow<T>.mergedStateMachineTake(count: Int): Flow<T> {
        return unsafeFlow() {
            try {
                val takeCollector = FlowTakeCollector(count, this)
                collect(takeCollector)
            } catch (e: StacklessCancellationException) {
                // Nothing, bail out
            }
        }
    }


    private class FlowTakeCollector<T>(
        private val count: Int,
        downstream: FlowCollector<T>
    ) : FlowCollector<T>, Continuation<Unit> {
        private var consumed = 0
        // Workaround for KT-30991
        private val emitFun = run {
            val suspendFun: suspend (T) -> Unit = { downstream.emit(it) }
            suspendFun as Function2<T, Continuation<Unit>, Any?>
        }

        private var caller: Continuation<Unit>? = null // lateinit

        override val context: CoroutineContext
            get() = caller?.context ?: EmptyCoroutineContext

        override fun resumeWith(result: Result<Unit>) {
            val completion = caller!!
            if (++consumed == count) completion.resumeWith(Result.failure(StacklessCancellationException()))
            else completion.resumeWith(Result.success(Unit))
        }

        override suspend fun emit(value: T) = suspendCoroutineUninterceptedOrReturn<Unit> sc@{
            // Invoke it in non-suspending way
            caller = it
            val result = emitFun.invoke(value, this)
            if (result !== COROUTINE_SUSPENDED) {
                if (++consumed == count) throw StacklessCancellationException()
                else return@sc Unit
            }
            COROUTINE_SUSPENDED
        }
    }
}
