/*
 * Copyright (c) 2014, Oracle America, Inc.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 *  * Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 *  * Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 *  * Neither the name of Oracle nor the names of its contributors may be used
 *    to endorse or promote products derived from this software without
 *    specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF
 * THE POSSIBILITY OF SUCH DAMAGE.
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
@Measurement(iterations = 5, time = 5, timeUnit = TimeUnit.SECONDS)
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
        guide.sync.example01.main(emptyArray())
    }

    @Benchmark
    fun sync02Volatile() {
        guide.sync.example02.main(emptyArray())
    }

    @Benchmark
    fun sync03AtomicInt() {
        guide.sync.example03.main(emptyArray())
    }

    @Benchmark
    fun sync04ConfineFine() {
        guide.sync.example04.main(emptyArray())
    }

    @Benchmark
    fun sync05ConfineCoarse() {
        guide.sync.example05.main(emptyArray())
    }

    @Benchmark
    fun sync06Mutex() {
        guide.sync.example06.main(emptyArray())
    }

    @Benchmark
    fun sync07Actor() {
        guide.sync.example07.main(emptyArray())
    }
}
