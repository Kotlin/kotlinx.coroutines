/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks

import org.openjdk.jmh.annotations.*
import java.io.OutputStream
import java.io.PrintStream
import java.util.concurrent.TimeUnit

/*

Benchmark                               Mode  Cnt        Score        Error  Units
GuideSyncBenchmark.sync01Problem        avgt   15    11971.221 ±   1739.891  us/op
GuideSyncBenchmark.sync02Volatile       avgt   15    14936.828 ±    142.586  us/op
GuideSyncBenchmark.sync03AtomicInt      avgt   15    15505.607 ±   1434.846  us/op
GuideSyncBenchmark.sync04ConfineFine    avgt   15  1331453.593 ±  89298.871  us/op
GuideSyncBenchmark.sync05ConfineCoarse  avgt   15     2253.270 ±    425.033  us/op
GuideSyncBenchmark.sync06Mutex          avgt   15  1075086.511 ± 140589.883  us/op
GuideSyncBenchmark.sync07Actor          avgt   15  1075603.512 ± 203901.350  us/op

 */

@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 3)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
open class GuideSyncBenchmark {
    val oldOut = System.out

    @Setup
    fun setup() {
        System.setOut(PrintStream(object : OutputStream() {
            override fun write(b: Int) {} // empty
        }))
    }

    @TearDown
    fun tearDonw() {
        System.setOut(oldOut)
    }

    @Benchmark
    fun sync01Problem() {
        kotlinx.coroutines.experimental.guide.sync01.main(emptyArray())
    }

    @Benchmark
    fun sync02Volatile() {
        kotlinx.coroutines.experimental.guide.sync02.main(emptyArray())
    }

    @Benchmark
    fun sync03AtomicInt() {
        kotlinx.coroutines.experimental.guide.sync03.main(emptyArray())
    }

    @Benchmark
    fun sync04ConfineFine() {
        kotlinx.coroutines.experimental.guide.sync04.main(emptyArray())
    }

    @Benchmark
    fun sync05ConfineCoarse() {
        kotlinx.coroutines.experimental.guide.sync05.main(emptyArray())
    }

    @Benchmark
    fun sync06Mutex() {
        kotlinx.coroutines.experimental.guide.sync06.main(emptyArray())
    }

    @Benchmark
    fun sync07Actor() {
        kotlinx.coroutines.experimental.guide.sync07.main(emptyArray())
    }
}
