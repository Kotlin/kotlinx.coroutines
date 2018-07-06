/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks

import kotlinx.coroutines.experimental.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*
import kotlin.coroutines.experimental.*
import kotlin.coroutines.experimental.intrinsics.*

@Warmup(iterations = 5)
@Measurement(iterations = 10)
@BenchmarkMode(Mode.Throughput)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
@Fork(2)
open class CancellableContinuationBenchmark {

    @Benchmark
    fun awaitWithSuspension(): Int {
        val deferred = CompletableDeferred<Int>()
        return run(allowSuspend = true) { deferred.await() }
    }

    @Benchmark
    fun awaitNoSuspension(): Int {
        val deferred = CompletableDeferred(1)
        return run { deferred.await() }
    }

    private fun run(allowSuspend: Boolean = false, block: suspend () -> Int): Int {
        val value = block.startCoroutineUninterceptedOrReturn(EmptyContinuation)
        if (value === COROUTINE_SUSPENDED) {
            if (!allowSuspend) {
                throw IllegalStateException("Unexpected suspend")
            } else {
                return -1
            }
        }

        return value as Int
    }

    object EmptyContinuation : Continuation<Int> {
        override val context: CoroutineContext
            get() = EmptyCoroutineContext

        override fun resume(value: Int) {
        }

        override fun resumeWithException(exception: Throwable) {
        }
    }
}
