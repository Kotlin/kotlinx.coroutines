/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.debug

import kotlinx.coroutines.*
import kotlinx.coroutines.debug.*
import org.openjdk.jmh.annotations.*
import org.openjdk.jmh.annotations.State
import java.util.concurrent.*

@Warmup(iterations = 5, time = 1)
@Measurement(iterations = 5, time = 1)
@Fork(value = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
open class DebugProbesConcurrentBenchmark {

    @Setup
    fun setup() {
        DebugProbes.sanitizeStackTraces = false
        DebugProbes.enableCreationStackTraces = false
        DebugProbes.install()
    }

    @TearDown
    fun tearDown() {
        DebugProbes.uninstall()
    }


    @Benchmark
    fun run() = runBlocking<Long> {
        var sum = 0L
        repeat(8) {
            launch(Dispatchers.Default) {
                val seq = stressSequenceBuilder((1..100).asSequence()) {
                    (1..it).asSequence()
                }

                for (i in seq) {
                    sum += i.toLong()
                }
            }
        }
        sum
    }

    private fun <Node> stressSequenceBuilder(initialSequence: Sequence<Node>, children: (Node) -> Sequence<Node>): Sequence<Node> {
        return sequence {
            val initialIterator = initialSequence.iterator()
            if (!initialIterator.hasNext()) {
                return@sequence
            }
            val visited = HashSet<Node>()
            val sequences = ArrayDeque<Sequence<Node>>()
            sequences.addLast(initialIterator.asSequence())
            while (sequences.isNotEmpty()) {
                val currentSequence = sequences.removeFirst()
                for (node in currentSequence) {
                    if (visited.add(node)) {
                        yield(node)
                        sequences.addLast(children(node))
                    }
                }
            }
        }
    }
}
